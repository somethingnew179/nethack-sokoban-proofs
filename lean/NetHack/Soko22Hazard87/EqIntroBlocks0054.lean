import NetHack.Soko22Hazard87.EqIntroBlocks0053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro13500 (p : Pattern) (selected : d12908 p = 2) : d12885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12898 q = 2) : d6211 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12898, d6211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13498 q selected
    | true =>
      simp only [d12898, d6211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro832 q selected
  have h2 (q : Pattern) (selected : d12899 q = 2) : d6212 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12899, d6212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12899, d6212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12900 q = 2) : d6213 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12900, d6213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12900, d6213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12902 q = 2) : d6214 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12902, d6214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12902, d6214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12907 q = 2) : d12884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12907, d12884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12907, d12884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12908 q = 2) : d12885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12908, d12885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12908, d12885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13501 (p : Pattern) (selected : d12914 p = 2) : d12891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12905 q = 2) : d12878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12905, d12878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13499 q selected
    | true =>
      simp only [d12905, d12878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12906 q = 2) : d12879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12906, d12879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12906, d12879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12909 q = 2) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12909, d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13500 q selected
    | true =>
      simp only [d12909, d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12910 q = 2) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12910, d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12910, d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12911 q = 2) : d12888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12911, d12888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12911, d12888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12912 q = 2) : d12889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12912, d12889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12912, d12889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12913 q = 2) : d12890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12913, d12890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12913, d12890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12914 q = 2) : d12891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12914, d12891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12914, d12891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13502 (p : Pattern) (selected : d12918 p = 2) : d12935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12909 q = 2) : d12886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12909, d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13500 q selected
    | true =>
      simp only [d12909, d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12910 q = 2) : d12887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12910, d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12910, d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12915 q = 2) : d12932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12915, d12932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12915, d12932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12916 q = 2) : d12933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12916, d12933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12916, d12933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12917 q = 2) : d12934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12917, d12934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12917, d12934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12918 q = 2) : d12935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12918, d12935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12918, d12935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13503 (p : Pattern) (selected : d12924 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12878 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13493 q selected
    | true =>
      simp only [d12878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12879 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12921 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12922 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12923 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12924 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13504 (p : Pattern) (selected : d12930 p = 2) : d150392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12892 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13494 q selected
    | true =>
      simp only [d12892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13496 q selected
  have h2 (q : Pattern) (selected : d12919 q = 2) : d150387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12919, d150387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13501 q selected
    | true =>
      simp only [d12919, d150387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13502 q selected
  have h3 (q : Pattern) (selected : d12920 q = 2) : d150388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12920, d150388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12920, d150388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12925 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13503 q selected
    | true =>
      simp only [d12925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12926 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12927 q = 2) : d150389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12927, d150389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12927, d150389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12928 q = 2) : d150390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12928, d150390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12928, d150390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12929 q = 2) : d150391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12929, d150391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12929, d150391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12930 q = 2) : d150392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12930, d150392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12930, d150392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13505 (p : Pattern) (selected : d12935 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12886 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13495 q selected
    | true =>
      simp only [d12886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12887 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12932 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12933 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12934 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12935 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13506 (p : Pattern) (selected : d12941 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12936 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13505 q selected
    | true =>
      simp only [d12936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12937 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12938 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12939 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12940 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12941 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13507 (p : Pattern) (selected : d12947 p = 2) : d150398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12714 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13457 q selected
  have h2 (q : Pattern) (selected : d12715 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12724 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13457 q selected
    | true =>
      simp only [d12724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13460 q selected
  have h4 (q : Pattern) (selected : d12725 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12726 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12827 q = 2) : d12724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12827, d12724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13476 q selected
    | true =>
      simp only [d12827, d12724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13485 q selected
  have h7 (q : Pattern) (selected : d12840 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13486 q selected
    | true =>
      simp only [d12840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13487 q selected
  have h8 (q : Pattern) (selected : d12841 q = 2) : d12725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12841, d12725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12841, d12725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12842 q = 2) : d150379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12842, d150379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12842, d150379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12843 q = 2) : d150380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12843, d150380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12843, d150380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12847 q = 2) : d150382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12847, d150382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12847, d150382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13488 q selected
  have h12 (q : Pattern) (selected : d12849 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13489 q selected
  have h13 (q : Pattern) (selected : d12850 q = 2) : d150383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12850, d150383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d12850, d150383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12851 q = 2) : d150384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12851, d150384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d12851, d150384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d12852 q = 2) : d150385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12852, d150385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d12852, d150385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d12853 q = 2) : d150386 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12853, d150386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12853, d150386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d12931 q = 2) : d150393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12931, d150393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12931, d150393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13504 q selected
  have h18 (q : Pattern) (selected : d12942 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13506 q selected
  have h19 (q : Pattern) (selected : d12943 q = 2) : d150394 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12943, d150394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12943, d150394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d12944 q = 2) : d150395 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12944, d150395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d12944, d150395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d12945 q = 2) : d150396 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12945, d150396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d12945, d150396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d12946 q = 2) : d150397 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12946, d150397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d12946, d150397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d12947 q = 2) : d150398 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d12947, d150398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d12947, d150398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13508 (p : Pattern) (selected : d12953 p = 2) : d150404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12948 q = 2) : d150399 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d12948, d150399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12948, d150399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13507 q selected
  have h2 (q : Pattern) (selected : d12949 q = 2) : d150400 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d12949, d150400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12949, d150400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12950 q = 2) : d150401 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d12950, d150401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12950, d150401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12951 q = 2) : d150402 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d12951, d150402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12951, d150402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12952 q = 2) : d150403 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d12952, d150403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12952, d150403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12953 q = 2) : d150404 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d12953, d150404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12953, d150404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13509 (p : Pattern) (selected : d12956 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1100 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1102 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1103 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1110 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
    | true =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1111 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1112 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1113 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1114 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12956 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13510 (p : Pattern) (selected : d12961 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1123 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1124 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1127 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12961 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13511 (p : Pattern) (selected : d12967 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12957 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13509 q selected
    | true =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
  have h2 (q : Pattern) (selected : d12958 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12959 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5024 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
    | true =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3844 q selected
  have h5 (q : Pattern) (selected : d5025 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5026 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12960 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12962 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
    | true =>
      simp only [d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13510 q selected
  have h9 (q : Pattern) (selected : d12963 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12964 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12965 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12966 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12967 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13512 (p : Pattern) (selected : d12971 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12962 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
    | true =>
      simp only [d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13510 q selected
  have h2 (q : Pattern) (selected : d12963 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12964 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12965 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12970 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12971 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13513 (p : Pattern) (selected : d12977 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12975 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12976 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12977 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13514 (p : Pattern) (selected : d12981 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12979 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12980 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12981 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13515 (p : Pattern) (selected : d12987 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12982 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13513 q selected
    | true =>
      simp only [d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13514 q selected
  have h2 (q : Pattern) (selected : d12983 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12984 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12985 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12986 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12987 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13516 (p : Pattern) (selected : d12990 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12975 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12976 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12990 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13517 (p : Pattern) (selected : d12991 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12979 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12980 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12991 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13518 (p : Pattern) (selected : d12997 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12982 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13513 q selected
    | true =>
      simp only [d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13514 q selected
  have h2 (q : Pattern) (selected : d12983 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12984 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12985 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12986 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12992 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13516 q selected
    | true =>
      simp only [d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13517 q selected
  have h7 (q : Pattern) (selected : d12993 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12994 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12995 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12996 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12997 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13519 (p : Pattern) (selected : d13002 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12975 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13001 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13002 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13520 (p : Pattern) (selected : d13004 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12979 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13003 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13004 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13521 (p : Pattern) (selected : d13011 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13009 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13010 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13011 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13522 (p : Pattern) (selected : d13014 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13012 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13013 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13014 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13523 (p : Pattern) (selected : d13018 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1210 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro865 q selected
    | true =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1211 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1212 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1213 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1100 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1102 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1103 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1214 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13018 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13524 (p : Pattern) (selected : d13024 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro692 q selected
    | true =>
      simp only [d1094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro843 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d1095 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d9452 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3842 q selected
    | true =>
      simp only [d9452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d9453 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d9795 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro662 q selected
    | true =>
      simp only [d133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d134 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d9796 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d9797 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9798 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d13024 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h11 p selected
theorem eqIntro13525 (p : Pattern) (selected : d13030 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9814 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10562 q selected
    | true =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9816 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13022 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13023 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13025 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13524 q selected
    | true =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13026 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13027 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13028 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13029 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13030 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13526 (p : Pattern) (selected : d13036 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13019 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13523 q selected
    | true =>
      simp only [d13019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13509 q selected
  have h2 (q : Pattern) (selected : d13020 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13021 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13031 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13509 q selected
    | true =>
      simp only [d13031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13525 q selected
  have h5 (q : Pattern) (selected : d13032 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13033 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13034 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12957 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13509 q selected
    | true =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
  have h9 (q : Pattern) (selected : d12958 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12959 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d5024 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
    | true =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3844 q selected
  have h12 (q : Pattern) (selected : d5025 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d5026 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12960 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13035 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13036 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13527 (p : Pattern) (selected : d13040 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12957 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13509 q selected
    | true =>
      simp only [d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
  have h2 (q : Pattern) (selected : d12958 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12959 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5024 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3841 q selected
    | true =>
      simp only [d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3844 q selected
  have h5 (q : Pattern) (selected : d5025 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5026 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12960 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d5027 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13039 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13040 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13528 (p : Pattern) (selected : d13046 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13526 q selected
    | true =>
      simp only [d13037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13041 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13527 q selected
    | true =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13042 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13043 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13044 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13045 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13046 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13529 (p : Pattern) (selected : d13050 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13041 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13527 q selected
    | true =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13042 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13047 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13048 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13049 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13050 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13530 (p : Pattern) (selected : d13052 p = 2) : d12956 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1255 q = 2) : d1100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro873 q selected
    | true =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1256 q = 2) : d1101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1256, d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1257 q = 2) : d1102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1257, d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1257, d1102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1258 q = 2) : d1103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1258, d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1258, d1103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1265 q = 2) : d1110 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
    | true =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1266 q = 2) : d1111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1267 q = 2) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1268 q = 2) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1268, d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1268, d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1269 q = 2) : d1114 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1269, d1114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1269, d1114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13052 q = 2) : d12956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13052, d12956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13052, d12956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13531 (p : Pattern) (selected : d13053 p = 2) : d5009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1265 q = 2) : d1110 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
    | true =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 2) : d1111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 2) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, d1112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1268 q = 2) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1268, d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1268, d1113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1277 q = 2) : d1122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1278 q = 2) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1279 q = 2) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1279, d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1280 q = 2) : d1125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1280, d1125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1280, d1125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13053 q = 2) : d5009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13053, d5009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13053, d5009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13532 (p : Pattern) (selected : d13060 p = 2) : d5023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d9943 q = 2) : d5018 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10580 q selected
    | true =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 2) : d5019 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13057 q = 2) : d5020 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13057, d5020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13057, d5020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13058 q = 2) : d5021 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13058, d5021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13058, d5021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13059 q = 2) : d5022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13059, d5022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13059, d5022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13060 q = 2) : d5023 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13060, d5023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13060, d5023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13533 (p : Pattern) (selected : d13065 p = 2) : d12961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 2) : d1122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 2) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, d1123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1279 q = 2) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1279, d1124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1282 q = 2) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1282, d1127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1282, d1127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13065 q = 2) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13065, d12961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13065, d12961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13534 (p : Pattern) (selected : d13071 p = 2) : d12967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13054 q = 2) : d12957 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13054, d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13530 q selected
    | true =>
      simp only [d13054, d12957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13531 q selected
  have h2 (q : Pattern) (selected : d13055 q = 2) : d12958 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13055, d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13055, d12958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13056 q = 2) : d12959 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13056, d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13056, d12959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13061 q = 2) : d5024 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13061, d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13531 q selected
    | true =>
      simp only [d13061, d5024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13532 q selected
  have h5 (q : Pattern) (selected : d13062 q = 2) : d5025 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13062, d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13062, d5025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13063 q = 2) : d5026 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13063, d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13063, d5026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13064 q = 2) : d12960 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13064, d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13064, d12960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13066 q = 2) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13066, d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13531 q selected
    | true =>
      simp only [d13066, d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13533 q selected
  have h9 (q : Pattern) (selected : d13067 q = 2) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13067, d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13067, d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13068 q = 2) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13068, d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13068, d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13069 q = 2) : d12965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13069, d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13069, d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13070 q = 2) : d12966 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13070, d12966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13070, d12966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13071 q = 2) : d12967 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13071, d12967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13071, d12967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13535 (p : Pattern) (selected : d13075 p = 2) : d12971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13066 q = 2) : d12962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13066, d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13531 q selected
    | true =>
      simp only [d13066, d12962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13533 q selected
  have h2 (q : Pattern) (selected : d13067 q = 2) : d12963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13067, d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13067, d12963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13068 q = 2) : d12964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13068, d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13068, d12964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13069 q = 2) : d12965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13069, d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13069, d12965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13074 q = 2) : d12970 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13074, d12970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13074, d12970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13075 q = 2) : d12971 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13075, d12971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13075, d12971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13536 (p : Pattern) (selected : d13081 p = 2) : d12977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13072 q = 2) : d12968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13072, d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13534 q selected
    | true =>
      simp only [d13072, d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13073 q = 2) : d12969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13073, d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13073, d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13076 q = 2) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13535 q selected
    | true =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13077 q = 2) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13078 q = 2) : d12974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13078, d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13078, d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13079 q = 2) : d12975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13079, d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13079, d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13080 q = 2) : d12976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13080, d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13080, d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13081 q = 2) : d12977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13081, d12977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13081, d12977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13537 (p : Pattern) (selected : d13085 p = 2) : d12981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13076 q = 2) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13535 q selected
    | true =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13077 q = 2) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13082 q = 2) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13082, d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13082, d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13083 q = 2) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13083, d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13083, d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13084 q = 2) : d12980 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13084, d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13084, d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13085 q = 2) : d12981 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13085, d12981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13085, d12981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13538 (p : Pattern) (selected : d13091 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13088 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13089 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13090 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13091 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13539 (p : Pattern) (selected : d13097 p = 2) : d12987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13005 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13519 q selected
    | true =>
      simp only [d13005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13520 q selected
  have h2 (q : Pattern) (selected : d13006 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13007 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13008 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13015 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13521 q selected
    | true =>
      simp only [d13015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13522 q selected
  have h6 (q : Pattern) (selected : d13016 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13017 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13051 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13528 q selected
    | true =>
      simp only [d13051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13529 q selected
  have h9 (q : Pattern) (selected : d13086 q = 2) : d12982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13086, d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13536 q selected
    | true =>
      simp only [d13086, d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13537 q selected
  have h10 (q : Pattern) (selected : d13087 q = 2) : d12983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13087, d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13087, d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13092 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13538 q selected
    | true =>
      simp only [d13092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13093 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13094 q = 2) : d12984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13094, d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13094, d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13095 q = 2) : d12985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13095, d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13095, d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13096 q = 2) : d12986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13096, d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13096, d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13097 q = 2) : d12987 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13097, d12987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13097, d12987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13540 (p : Pattern) (selected : d13098 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12975 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13001 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13098 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13541 (p : Pattern) (selected : d13099 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12979 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13003 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13099 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13542 (p : Pattern) (selected : d13104 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12974 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13009 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13010 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13104 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13543 (p : Pattern) (selected : d13105 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12978 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13012 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13013 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13105 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13544 (p : Pattern) (selected : d13109 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13037 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13526 q selected
    | true =>
      simp only [d13037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13038 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13041 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13527 q selected
    | true =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13042 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13043 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13044 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13045 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13109 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13545 (p : Pattern) (selected : d13110 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13041 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13527 q selected
    | true =>
      simp only [d13041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13042 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12972 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13512 q selected
    | true =>
      simp only [d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12973 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13047 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13048 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13049 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13110 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13546 (p : Pattern) (selected : d13112 p = 2) : d12990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13072 q = 2) : d12968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13072, d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13534 q selected
    | true =>
      simp only [d13072, d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13073 q = 2) : d12969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13073, d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13073, d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13076 q = 2) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13535 q selected
    | true =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13077 q = 2) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13078 q = 2) : d12974 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13078, d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13078, d12974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13079 q = 2) : d12975 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13079, d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13079, d12975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13080 q = 2) : d12976 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13080, d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13080, d12976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13112 q = 2) : d12990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13112, d12990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13112, d12990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13547 (p : Pattern) (selected : d13113 p = 2) : d12991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13076 q = 2) : d12972 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13535 q selected
    | true =>
      simp only [d13076, d12972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13077 q = 2) : d12973 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13077, d12973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13082 q = 2) : d12978 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13082, d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13082, d12978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13083 q = 2) : d12979 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13083, d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13083, d12979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13084 q = 2) : d12980 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13084, d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13084, d12980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13113 q = 2) : d12991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13113, d12991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13113, d12991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13548 (p : Pattern) (selected : d13116 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12968 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13511 q selected
    | true =>
      simp only [d12968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12969 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13088 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13089 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13090 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13116 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13549 (p : Pattern) (selected : d13122 p = 2) : d12997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13005 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13519 q selected
    | true =>
      simp only [d13005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13520 q selected
  have h2 (q : Pattern) (selected : d13006 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13007 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13008 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13015 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13521 q selected
    | true =>
      simp only [d13015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13522 q selected
  have h6 (q : Pattern) (selected : d13016 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13017 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13051 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13528 q selected
    | true =>
      simp only [d13051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13529 q selected
  have h9 (q : Pattern) (selected : d13086 q = 2) : d12982 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13086, d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13536 q selected
    | true =>
      simp only [d13086, d12982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13537 q selected
  have h10 (q : Pattern) (selected : d13087 q = 2) : d12983 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13087, d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13087, d12983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13092 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13538 q selected
    | true =>
      simp only [d13092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13093 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13094 q = 2) : d12984 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13094, d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13094, d12984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13095 q = 2) : d12985 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13095, d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13095, d12985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13096 q = 2) : d12986 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13096, d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13096, d12986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13100 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13540 q selected
    | true =>
      simp only [d13100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13541 q selected
  have h17 (q : Pattern) (selected : d13101 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d13102 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d13103 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13106 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13542 q selected
    | true =>
      simp only [d13106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13543 q selected
  have h21 (q : Pattern) (selected : d13107 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d13108 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13111 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13544 q selected
    | true =>
      simp only [d13111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13545 q selected
  have h24 (q : Pattern) (selected : d13114 q = 2) : d12992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13114, d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13546 q selected
    | true =>
      simp only [d13114, d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13547 q selected
  have h25 (q : Pattern) (selected : d13115 q = 2) : d12993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13115, d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d13115, d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d13117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13548 q selected
    | true =>
      simp only [d13117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d13118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d13118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d13119 q = 2) : d12994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13119, d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d13119, d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d13120 q = 2) : d12995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13120, d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d13120, d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d13121 q = 2) : d12996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13121, d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13121, d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d13122 q = 2) : d12997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13122, d12997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13122, d12997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13550 (p : Pattern) (selected : d13134 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13529 q selected
    | true =>
      simp only [d13124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13514 q selected
  have h2 (q : Pattern) (selected : d13125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13127 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13128 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13129 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13514 q selected
    | true =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13130 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13131 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13132 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13133 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13134 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13551 (p : Pattern) (selected : d13140 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13129 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13514 q selected
    | true =>
      simp only [d13129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13130 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13131 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13132 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13133 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13135 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13517 q selected
    | true =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13136 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13137 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13138 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13139 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13140 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13552 (p : Pattern) (selected : d13147 p = 2) : d150409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13111 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13544 q selected
    | true =>
      simp only [d13111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13545 q selected
  have h2 (q : Pattern) (selected : d13114 q = 2) : d12992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13114, d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13546 q selected
    | true =>
      simp only [d13114, d12992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13547 q selected
  have h3 (q : Pattern) (selected : d13115 q = 2) : d12993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13115, d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13115, d12993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13548 q selected
    | true =>
      simp only [d13117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13119 q = 2) : d12994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13119, d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13119, d12994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13145 q = 2) : d12995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13145, d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13145, d12995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13146 q = 2) : d12996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13146, d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13146, d12996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13147 q = 2) : d150409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13147, d150409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13147, d150409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13553 (p : Pattern) (selected : d13149 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13135 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13517 q selected
    | true =>
      simp only [d13135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13136 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13137 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13138 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13139 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13149 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13554 (p : Pattern) (selected : d13155 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1376 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro865 q selected
  have h2 (q : Pattern) (selected : d1210 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro865 q selected
    | true =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1377 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1211 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1378 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1379 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1380 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
  have h8 (q : Pattern) (selected : d1100 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1381 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1382 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1383 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1384 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13155 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13555 (p : Pattern) (selected : d13156 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1380 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
  have h2 (q : Pattern) (selected : d1100 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1381 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1382 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1383 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1385 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
  have h8 (q : Pattern) (selected : d1110 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
    | true =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1386 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1111 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1387 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1388 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1389 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13156 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13556 (p : Pattern) (selected : d13169 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13160 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10562 q selected
  have h2 (q : Pattern) (selected : d9814 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10562 q selected
    | true =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13161 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9816 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13162 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13163 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13164 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13524 q selected
  have h8 (q : Pattern) (selected : d13025 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13524 q selected
    | true =>
      simp only [d13025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13165 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13026 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13166 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13167 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13168 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13169 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13557 (p : Pattern) (selected : d13179 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13157 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13554 q selected
    | true =>
      simp only [d13157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13555 q selected
  have h2 (q : Pattern) (selected : d13158 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13159 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13170 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13555 q selected
    | true =>
      simp only [d13170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13556 q selected
  have h5 (q : Pattern) (selected : d13171 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13172 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13173 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13174 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13555 q selected
    | true =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
  have h9 (q : Pattern) (selected : d13175 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13176 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6356 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4538 q selected
  have h12 (q : Pattern) (selected : d6357 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6358 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13177 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13178 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13179 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13558 (p : Pattern) (selected : d13183 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13174 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13555 q selected
    | true =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
  have h2 (q : Pattern) (selected : d13175 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13176 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6356 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4538 q selected
  have h5 (q : Pattern) (selected : d6357 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6358 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13177 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6359 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13182 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13183 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13559 (p : Pattern) (selected : d13189 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13180 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13557 q selected
    | true =>
      simp only [d13180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13181 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13184 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13558 q selected
    | true =>
      simp only [d13184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13185 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13186 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13187 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13188 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13189 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13560 (p : Pattern) (selected : d13190 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
  have h2 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1122 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1393 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1394 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1400 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13190 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13561 (p : Pattern) (selected : d13196 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13191 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13560 q selected
  have h2 (q : Pattern) (selected : d13192 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13193 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13194 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13195 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13196 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13562 (p : Pattern) (selected : d13202 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13184 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13558 q selected
    | true =>
      simp only [d13184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13185 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13197 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13561 q selected
    | true =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13198 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13199 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13200 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13201 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13202 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13563 (p : Pattern) (selected : d13204 p = 2) : d13156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1438 q = 2) : d1380 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1438, d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1438, d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro873 q selected
  have h2 (q : Pattern) (selected : d1255 q = 2) : d1100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro873 q selected
    | true =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1439 q = 2) : d1381 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1439, d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1439, d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1256 q = 2) : d1101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1256, d1101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1440 q = 2) : d1382 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1440, d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1440, d1382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1441 q = 2) : d1383 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1441, d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1441, d1383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1442 q = 2) : d1385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
  have h8 (q : Pattern) (selected : d1265 q = 2) : d1110 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
    | true =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1443 q = 2) : d1386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1266 q = 2) : d1111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1444 q = 2) : d1387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1444, d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1445 q = 2) : d1388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1445, d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1445, d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1446 q = 2) : d1389 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1446, d1389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1446, d1389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13204 q = 2) : d13156 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13204, d13156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13204, d13156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13564 (p : Pattern) (selected : d13205 p = 2) : d6349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1442 q = 2) : d1385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
  have h2 (q : Pattern) (selected : d1265 q = 2) : d1110 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
    | true =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 2) : d1386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 2) : d1111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, d1111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 2) : d1387 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, d1387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1445 q = 2) : d1388 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1445, d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1445, d1388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1447 q = 2) : d1391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
  have h8 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1448 q = 2) : d1392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1277 q = 2) : d1122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1449 q = 2) : d1393 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1449, d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1450 q = 2) : d1394 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1450, d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1451 q = 2) : d1395 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1451, d1395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1451, d1395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13205 q = 2) : d6349 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13205, d6349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13205, d6349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13565 (p : Pattern) (selected : d13214 p = 2) : d6355 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13209 q = 2) : d6350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13209, d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13209, d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10580 q selected
  have h2 (q : Pattern) (selected : d9943 q = 2) : d5018 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10580 q selected
    | true =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13210 q = 2) : d6351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13210, d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13210, d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9945 q = 2) : d5019 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9945, d5019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13211 q = 2) : d6352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13211, d6352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13211, d6352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13212 q = 2) : d6353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13212, d6353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13212, d6353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13213 q = 2) : d6354 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13213, d6354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13213, d6354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13214 q = 2) : d6355 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13214, d6355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13214, d6355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13566 (p : Pattern) (selected : d13219 p = 2) : d13190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1447 q = 2) : d1391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
  have h2 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 2) : d1392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 2) : d1122 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, d1122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 2) : d1393 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, d1393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1450 q = 2) : d1394 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1450, d1394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1453 q = 2) : d1400 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1453, d1400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1453, d1400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13219 q = 2) : d13190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13219, d13190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13219, d13190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13567 (p : Pattern) (selected : d13225 p = 2) : d13243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13206 q = 2) : d13174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13206, d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13563 q selected
    | true =>
      simp only [d13206, d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13564 q selected
  have h2 (q : Pattern) (selected : d13207 q = 2) : d13175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13207, d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13207, d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13208 q = 2) : d13176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13208, d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13208, d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13215 q = 2) : d6356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13215, d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13564 q selected
    | true =>
      simp only [d13215, d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13565 q selected
  have h5 (q : Pattern) (selected : d13216 q = 2) : d6357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13216, d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13216, d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13217 q = 2) : d6358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13217, d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13217, d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13218 q = 2) : d13177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13218, d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13218, d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13220 q = 2) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13220, d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13564 q selected
    | true =>
      simp only [d13220, d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13566 q selected
  have h9 (q : Pattern) (selected : d13221 q = 2) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13221, d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13221, d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13222 q = 2) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13222, d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13222, d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13223 q = 2) : d13194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13223, d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13223, d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13224 q = 2) : d13242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13224, d13242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13224, d13242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13225 q = 2) : d13243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13225, d13243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13225, d13243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13568 (p : Pattern) (selected : d13229 p = 2) : d13196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13220 q = 2) : d13191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13220, d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13564 q selected
    | true =>
      simp only [d13220, d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13566 q selected
  have h2 (q : Pattern) (selected : d13221 q = 2) : d13192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13221, d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13221, d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13222 q = 2) : d13193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13222, d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13222, d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13223 q = 2) : d13194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13223, d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13223, d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13228 q = 2) : d13195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13228, d13195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13228, d13195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13229 q = 2) : d13196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13229, d13196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13229, d13196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13569 (p : Pattern) (selected : d13235 p = 2) : d150418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13226 q = 2) : d13244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13226, d13244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13567 q selected
    | true =>
      simp only [d13226, d13244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13227 q = 2) : d13245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13227, d13245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13227, d13245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13230 q = 2) : d13197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13230, d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13568 q selected
    | true =>
      simp only [d13230, d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13231 q = 2) : d13198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13231, d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13231, d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13232 q = 2) : d150415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13232, d150415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13232, d150415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13233 q = 2) : d150416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13233, d150416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13233, d150416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13234 q = 2) : d150417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13234, d150417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13234, d150417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13235 q = 2) : d150418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13235, d150418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13235, d150418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13570 (p : Pattern) (selected : d13239 p = 2) : d13260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13230 q = 2) : d13197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13230, d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13568 q selected
    | true =>
      simp only [d13230, d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13231 q = 2) : d13198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13231, d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13231, d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13236 q = 2) : d13257 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13236, d13257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13236, d13257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13237 q = 2) : d13258 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13237, d13258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13237, d13258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13238 q = 2) : d13259 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13238, d13259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13238, d13259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13239 q = 2) : d13260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13239, d13260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13239, d13260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13571 (p : Pattern) (selected : d13243 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13174 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13555 q selected
    | true =>
      simp only [d13174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
  have h2 (q : Pattern) (selected : d13175 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13176 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6356 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d6356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4538 q selected
  have h5 (q : Pattern) (selected : d6357 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6358 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13177 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13191 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4537 q selected
    | true =>
      simp only [d13191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13560 q selected
  have h9 (q : Pattern) (selected : d13192 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13193 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13194 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13242 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13243 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13572 (p : Pattern) (selected : d13249 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13244 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13571 q selected
    | true =>
      simp only [d13244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13245 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13246 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13247 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13248 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13249 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13573 (p : Pattern) (selected : d13255 p = 2) : d150424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13203 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13559 q selected
    | true =>
      simp only [d13203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13562 q selected
  have h2 (q : Pattern) (selected : d13240 q = 2) : d150419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13240, d150419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13569 q selected
    | true =>
      simp only [d13240, d150419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13570 q selected
  have h3 (q : Pattern) (selected : d13241 q = 2) : d150420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13241, d150420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13241, d150420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13250 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13572 q selected
    | true =>
      simp only [d13250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13251 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13252 q = 2) : d150421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13252, d150421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13252, d150421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13253 q = 2) : d150422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13253, d150422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13253, d150422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13254 q = 2) : d150423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13254, d150423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13254, d150423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13255 q = 2) : d150424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13255, d150424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13255, d150424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13574 (p : Pattern) (selected : d13260 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13197 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13561 q selected
    | true =>
      simp only [d13197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13198 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13257 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13258 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13259 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13260 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13575 (p : Pattern) (selected : d13266 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13261 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13574 q selected
    | true =>
      simp only [d13261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13262 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13263 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13264 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13265 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13266 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13576 (p : Pattern) (selected : d13272 p = 2) : d150430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12988 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13515 q selected
  have h2 (q : Pattern) (selected : d12989 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12998 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13515 q selected
    | true =>
      simp only [d12998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13518 q selected
  have h4 (q : Pattern) (selected : d12999 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13000 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13123 q = 2) : d12998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13123, d12998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13539 q selected
    | true =>
      simp only [d13123, d12998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13549 q selected
  have h7 (q : Pattern) (selected : d13141 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13550 q selected
    | true =>
      simp only [d13141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13551 q selected
  have h8 (q : Pattern) (selected : d13142 q = 2) : d12999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13142, d12999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13142, d12999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13143 q = 2) : d150407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13143, d150407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13143, d150407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13144 q = 2) : d150408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13144, d150408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13144, d150408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13148 q = 2) : d150410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13148, d150410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13148, d150410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13552 q selected
  have h12 (q : Pattern) (selected : d13150 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13553 q selected
  have h13 (q : Pattern) (selected : d13151 q = 2) : d150411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13151, d150411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13151, d150411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13152 q = 2) : d150412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13152, d150412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13152, d150412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d13153 q = 2) : d150413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13153, d150413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d13153, d150413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d13154 q = 2) : d150414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13154, d150414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13154, d150414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d13256 q = 2) : d150425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13256, d150425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13256, d150425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13573 q selected
  have h18 (q : Pattern) (selected : d13267 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13575 q selected
  have h19 (q : Pattern) (selected : d13268 q = 2) : d150426 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13268, d150426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13268, d150426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13269 q = 2) : d150427 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13269, d150427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13269, d150427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d13270 q = 2) : d150428 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13270, d150428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d13270, d150428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d13271 q = 2) : d150429 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13271, d150429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13271, d150429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13272 q = 2) : d150430 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d13272, d150430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d13272, d150430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13577 (p : Pattern) (selected : d13278 p = 2) : d150436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13273 q = 2) : d150431 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d13273, d150431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13273, d150431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13576 q selected
  have h2 (q : Pattern) (selected : d13274 q = 2) : d150432 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d13274, d150432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13274, d150432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13275 q = 2) : d150433 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d13275, d150433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13275, d150433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13276 q = 2) : d150434 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d13276, d150434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13276, d150434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13277 q = 2) : d150435 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d13277, d150435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13277, d150435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13278 q = 2) : d150436 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d13278, d150436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13278, d150436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13578 (p : Pattern) (selected : d13282 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1556 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1557 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1558 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1570 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1572 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1573 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1574 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13282 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13579 (p : Pattern) (selected : d13287 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1584 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1585 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1588 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13287 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13580 (p : Pattern) (selected : d13293 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13283 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13578 q selected
    | true =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
  have h2 (q : Pattern) (selected : d13284 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13285 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5140 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
    | true =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3859 q selected
  have h5 (q : Pattern) (selected : d5141 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5142 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13286 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13288 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
    | true =>
      simp only [d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13579 q selected
  have h9 (q : Pattern) (selected : d13289 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13290 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13291 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13292 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13293 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13581 (p : Pattern) (selected : d13297 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13288 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
    | true =>
      simp only [d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13579 q selected
  have h2 (q : Pattern) (selected : d13289 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13290 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13291 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13296 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13297 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13582 (p : Pattern) (selected : d13303 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13301 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13302 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13303 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13583 (p : Pattern) (selected : d13307 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13305 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13306 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13307 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13584 (p : Pattern) (selected : d13313 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13308 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13582 q selected
    | true =>
      simp only [d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13583 q selected
  have h2 (q : Pattern) (selected : d13309 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13310 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13311 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13312 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13313 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13585 (p : Pattern) (selected : d13316 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13301 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13302 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13316 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13586 (p : Pattern) (selected : d13317 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13305 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13306 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13317 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13587 (p : Pattern) (selected : d13323 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13308 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13582 q selected
    | true =>
      simp only [d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13583 q selected
  have h2 (q : Pattern) (selected : d13309 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13310 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13311 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13312 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13318 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13585 q selected
    | true =>
      simp only [d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13586 q selected
  have h7 (q : Pattern) (selected : d13319 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13320 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13321 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13322 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13323 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13588 (p : Pattern) (selected : d13328 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13301 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13327 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13328 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13589 (p : Pattern) (selected : d13330 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13305 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13329 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13330 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13590 (p : Pattern) (selected : d13337 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13335 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13336 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13337 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13591 (p : Pattern) (selected : d13340 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13338 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13339 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13340 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13592 (p : Pattern) (selected : d13344 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1665 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1666 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1667 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1668 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1556 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1557 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1558 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1669 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13344 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13593 (p : Pattern) (selected : d13350 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro921 q selected
    | true =>
      simp only [d1543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro922 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d1544 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro843 q selected
  have h3 (q : Pattern) (selected : d1545 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10057 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3857 q selected
    | true =>
      simp only [d10057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d10058 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d10080 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1549 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro923 q selected
    | true =>
      simp only [d1549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d1550 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d10081 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d10082 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10083 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d13350 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro13594 (p : Pattern) (selected : d13356 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10099 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
    | true =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13351 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13593 q selected
    | true =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13352 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13353 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13354 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13355 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13356 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13595 (p : Pattern) (selected : d13362 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13345 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13592 q selected
    | true =>
      simp only [d13345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13578 q selected
  have h2 (q : Pattern) (selected : d13346 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13347 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13357 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13578 q selected
    | true =>
      simp only [d13357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13594 q selected
  have h5 (q : Pattern) (selected : d13358 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13359 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13360 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13283 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13578 q selected
    | true =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
  have h9 (q : Pattern) (selected : d13284 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13285 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d5140 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
    | true =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3859 q selected
  have h12 (q : Pattern) (selected : d5141 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d5142 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13286 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13361 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13362 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13596 (p : Pattern) (selected : d13366 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13283 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13578 q selected
    | true =>
      simp only [d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
  have h2 (q : Pattern) (selected : d13284 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13285 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5140 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3856 q selected
    | true =>
      simp only [d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3859 q selected
  have h5 (q : Pattern) (selected : d5141 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5142 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13286 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d5143 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13365 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13366 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13597 (p : Pattern) (selected : d13372 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13363 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13595 q selected
    | true =>
      simp only [d13363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13364 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13367 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13596 q selected
    | true =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13368 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13369 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13370 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13371 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13372 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13598 (p : Pattern) (selected : d13376 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13367 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13596 q selected
    | true =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13368 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13373 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13374 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13375 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13376 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13599 (p : Pattern) (selected : d13378 p = 2) : d13282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1726 q = 2) : d1555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
    | true =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 2) : d1556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1728 q = 2) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1728, d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1728, d1557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1729 q = 2) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1729, d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1729, d1558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1743 q = 2) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1744 q = 2) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1745 q = 2) : d1574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1745, d1574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1745, d1574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13378 q = 2) : d13282 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13378, d13282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13378, d13282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13600 (p : Pattern) (selected : d13379 p = 2) : d5120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 2) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, d1572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1744 q = 2) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1744, d1573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1755 q = 2) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1756 q = 2) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1757 q = 2) : d1586 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1757, d1586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1757, d1586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13379 q = 2) : d5120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13379, d5120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13379, d5120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13601 (p : Pattern) (selected : d13386 p = 2) : d5139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10243 q = 2) : d5134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
    | true =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 2) : d5135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13383 q = 2) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13383, d5136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13383, d5136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13384 q = 2) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13384, d5137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13384, d5137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13385 q = 2) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13385, d5138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13385, d5138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13386 q = 2) : d5139 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13386, d5139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13386, d5139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13602 (p : Pattern) (selected : d13391 p = 2) : d13287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 2) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, d1584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1756 q = 2) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1756, d1585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1759 q = 2) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1759, d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1759, d1588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13391 q = 2) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13391, d13287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13391, d13287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13603 (p : Pattern) (selected : d13397 p = 2) : d13293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13380 q = 2) : d13283 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13380, d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13599 q selected
    | true =>
      simp only [d13380, d13283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13600 q selected
  have h2 (q : Pattern) (selected : d13381 q = 2) : d13284 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13381, d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13381, d13284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13382 q = 2) : d13285 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13382, d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13382, d13285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13387 q = 2) : d5140 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13387, d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13600 q selected
    | true =>
      simp only [d13387, d5140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13601 q selected
  have h5 (q : Pattern) (selected : d13388 q = 2) : d5141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13388, d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13388, d5141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13389 q = 2) : d5142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13389, d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13389, d5142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13390 q = 2) : d13286 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13390, d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13390, d13286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13392 q = 2) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13392, d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13600 q selected
    | true =>
      simp only [d13392, d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13602 q selected
  have h9 (q : Pattern) (selected : d13393 q = 2) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13393, d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13393, d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13394 q = 2) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13394, d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13394, d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13395 q = 2) : d13291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13395, d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13395, d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13396 q = 2) : d13292 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13396, d13292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13396, d13292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13397 q = 2) : d13293 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13397, d13293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13397, d13293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13604 (p : Pattern) (selected : d13401 p = 2) : d13297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13392 q = 2) : d13288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13392, d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13600 q selected
    | true =>
      simp only [d13392, d13288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13602 q selected
  have h2 (q : Pattern) (selected : d13393 q = 2) : d13289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13393, d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13393, d13289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13394 q = 2) : d13290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13394, d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13394, d13290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13395 q = 2) : d13291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13395, d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13395, d13291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13400 q = 2) : d13296 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13400, d13296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13400, d13296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13401 q = 2) : d13297 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13401, d13297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13401, d13297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13605 (p : Pattern) (selected : d13407 p = 2) : d13303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13398 q = 2) : d13294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13398, d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13603 q selected
    | true =>
      simp only [d13398, d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13399 q = 2) : d13295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13399, d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13399, d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13402 q = 2) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13604 q selected
    | true =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13403 q = 2) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13404 q = 2) : d13300 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13404, d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13404, d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13405 q = 2) : d13301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13405, d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13405, d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13406 q = 2) : d13302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13406, d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13406, d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13407 q = 2) : d13303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13407, d13303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13407, d13303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13606 (p : Pattern) (selected : d13411 p = 2) : d13307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13402 q = 2) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13604 q selected
    | true =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13403 q = 2) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13408 q = 2) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13408, d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13408, d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13409 q = 2) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13409, d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13409, d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13410 q = 2) : d13306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13410, d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13410, d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13411 q = 2) : d13307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13411, d13307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13411, d13307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13607 (p : Pattern) (selected : d13417 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13414 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13415 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13416 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13417 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13608 (p : Pattern) (selected : d13423 p = 2) : d13313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13331 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13588 q selected
    | true =>
      simp only [d13331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13589 q selected
  have h2 (q : Pattern) (selected : d13332 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13333 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13334 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13341 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13590 q selected
    | true =>
      simp only [d13341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13591 q selected
  have h6 (q : Pattern) (selected : d13342 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13343 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13377 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13597 q selected
    | true =>
      simp only [d13377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13598 q selected
  have h9 (q : Pattern) (selected : d13412 q = 2) : d13308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13412, d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13605 q selected
    | true =>
      simp only [d13412, d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13606 q selected
  have h10 (q : Pattern) (selected : d13413 q = 2) : d13309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13413, d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13413, d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13418 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13607 q selected
    | true =>
      simp only [d13418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13419 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13420 q = 2) : d13310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13420, d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13420, d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13421 q = 2) : d13311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13421, d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13421, d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13422 q = 2) : d13312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13422, d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13422, d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13423 q = 2) : d13313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13423, d13313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13423, d13313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13609 (p : Pattern) (selected : d13424 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13301 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13327 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13424 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13610 (p : Pattern) (selected : d13425 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13305 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13329 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13425 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13611 (p : Pattern) (selected : d13430 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13300 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13335 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13336 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13430 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13612 (p : Pattern) (selected : d13431 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13304 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13338 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13339 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13431 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13613 (p : Pattern) (selected : d13435 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13363 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13595 q selected
    | true =>
      simp only [d13363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13364 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13367 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13596 q selected
    | true =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13368 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13369 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13370 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13371 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13435 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13614 (p : Pattern) (selected : d13436 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13367 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13596 q selected
    | true =>
      simp only [d13367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13368 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13298 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13581 q selected
    | true =>
      simp only [d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13299 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13373 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13374 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13375 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13436 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13615 (p : Pattern) (selected : d13438 p = 2) : d13316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13398 q = 2) : d13294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13398, d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13603 q selected
    | true =>
      simp only [d13398, d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13399 q = 2) : d13295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13399, d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13399, d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13402 q = 2) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13604 q selected
    | true =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13403 q = 2) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13404 q = 2) : d13300 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13404, d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13404, d13300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13405 q = 2) : d13301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13405, d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13405, d13301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13406 q = 2) : d13302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13406, d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13406, d13302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13438 q = 2) : d13316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13438, d13316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13438, d13316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13616 (p : Pattern) (selected : d13439 p = 2) : d13317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13402 q = 2) : d13298 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13604 q selected
    | true =>
      simp only [d13402, d13298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13403 q = 2) : d13299 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13403, d13299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13408 q = 2) : d13304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13408, d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13408, d13304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13409 q = 2) : d13305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13409, d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13409, d13305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13410 q = 2) : d13306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13410, d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13410, d13306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13439 q = 2) : d13317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13439, d13317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13439, d13317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13617 (p : Pattern) (selected : d13442 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13294 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13580 q selected
    | true =>
      simp only [d13294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13295 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13414 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13415 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13416 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13442 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13618 (p : Pattern) (selected : d13448 p = 2) : d13323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13331 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13588 q selected
    | true =>
      simp only [d13331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13589 q selected
  have h2 (q : Pattern) (selected : d13332 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13333 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13334 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13341 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13590 q selected
    | true =>
      simp only [d13341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13591 q selected
  have h6 (q : Pattern) (selected : d13342 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13343 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13377 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13597 q selected
    | true =>
      simp only [d13377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13598 q selected
  have h9 (q : Pattern) (selected : d13412 q = 2) : d13308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13412, d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13605 q selected
    | true =>
      simp only [d13412, d13308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13606 q selected
  have h10 (q : Pattern) (selected : d13413 q = 2) : d13309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13413, d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13413, d13309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13418 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13607 q selected
    | true =>
      simp only [d13418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13419 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13420 q = 2) : d13310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13420, d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13420, d13310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13421 q = 2) : d13311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13421, d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13421, d13311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13422 q = 2) : d13312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13422, d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13422, d13312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13426 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13609 q selected
    | true =>
      simp only [d13426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13610 q selected
  have h17 (q : Pattern) (selected : d13427 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d13428 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d13429 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13432 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13611 q selected
    | true =>
      simp only [d13432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13612 q selected
  have h21 (q : Pattern) (selected : d13433 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d13434 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13437 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13613 q selected
    | true =>
      simp only [d13437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13614 q selected
  have h24 (q : Pattern) (selected : d13440 q = 2) : d13318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13440, d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13615 q selected
    | true =>
      simp only [d13440, d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13616 q selected
  have h25 (q : Pattern) (selected : d13441 q = 2) : d13319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13441, d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d13441, d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d13443 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13617 q selected
    | true =>
      simp only [d13443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d13444 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d13444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d13445 q = 2) : d13320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13445, d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d13445, d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d13446 q = 2) : d13321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13446, d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d13446, d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d13447 q = 2) : d13322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13447, d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13447, d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d13448 q = 2) : d13323 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13448, d13323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13448, d13323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13619 (p : Pattern) (selected : d13460 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13450 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13598 q selected
    | true =>
      simp only [d13450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13583 q selected
  have h2 (q : Pattern) (selected : d13451 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13452 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13453 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13454 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13455 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13583 q selected
    | true =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13456 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13457 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13458 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13459 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13460 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13620 (p : Pattern) (selected : d13466 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13455 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13583 q selected
    | true =>
      simp only [d13455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13456 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13457 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13458 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13459 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13461 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13586 q selected
    | true =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13462 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13463 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13464 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13465 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13466 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13621 (p : Pattern) (selected : d13473 p = 2) : d150442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13437 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13613 q selected
    | true =>
      simp only [d13437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13614 q selected
  have h2 (q : Pattern) (selected : d13440 q = 2) : d13318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13440, d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13615 q selected
    | true =>
      simp only [d13440, d13318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13616 q selected
  have h3 (q : Pattern) (selected : d13441 q = 2) : d13319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13441, d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13441, d13319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13443 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13617 q selected
    | true =>
      simp only [d13443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13444 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13445 q = 2) : d13320 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13445, d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13445, d13320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13471 q = 2) : d13321 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13471, d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13471, d13321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13472 q = 2) : d13322 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13472, d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13472, d13322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13473 q = 2) : d150442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13473, d150442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13473, d150442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13622 (p : Pattern) (selected : d13475 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13461 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13586 q selected
    | true =>
      simp only [d13461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13462 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13463 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13464 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13465 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13475 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13623 (p : Pattern) (selected : d13481 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1853 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
  have h2 (q : Pattern) (selected : d1665 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1854 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1666 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1855 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1856 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1857 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
  have h8 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1858 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1556 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1859 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1860 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1861 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13481 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13624 (p : Pattern) (selected : d13482 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1857 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
  have h2 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1858 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1556 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1859 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1860 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1862 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
  have h8 (q : Pattern) (selected : d1570 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1863 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1864 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1865 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1866 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13482 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13625 (p : Pattern) (selected : d13495 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13486 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
  have h2 (q : Pattern) (selected : d10099 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
    | true =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13487 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10101 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13488 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13489 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13490 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13593 q selected
  have h8 (q : Pattern) (selected : d13351 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13593 q selected
    | true =>
      simp only [d13351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13491 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13352 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13492 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13493 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13494 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13495 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13626 (p : Pattern) (selected : d13505 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13483 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13623 q selected
    | true =>
      simp only [d13483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13624 q selected
  have h2 (q : Pattern) (selected : d13484 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13485 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13496 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13624 q selected
    | true =>
      simp only [d13496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13625 q selected
  have h5 (q : Pattern) (selected : d13497 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13498 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13499 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13500 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13624 q selected
    | true =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
  have h9 (q : Pattern) (selected : d13501 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13502 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6502 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4565 q selected
  have h12 (q : Pattern) (selected : d6503 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6504 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13503 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13504 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13505 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13627 (p : Pattern) (selected : d13509 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13500 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13624 q selected
    | true =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
  have h2 (q : Pattern) (selected : d13501 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13502 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6502 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4565 q selected
  have h5 (q : Pattern) (selected : d6503 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6504 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13503 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6505 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13508 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13509 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13628 (p : Pattern) (selected : d13515 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13506 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13626 q selected
    | true =>
      simp only [d13506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13507 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13510 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13627 q selected
    | true =>
      simp only [d13510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13511 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13512 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13513 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13514 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13515 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13629 (p : Pattern) (selected : d13516 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1868 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
  have h2 (q : Pattern) (selected : d1582 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro928 q selected
    | true =>
      simp only [d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1869 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1583 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1870 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1871 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1877 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13516 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13630 (p : Pattern) (selected : d13522 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13517 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13629 q selected
  have h2 (q : Pattern) (selected : d13518 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13519 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13520 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13521 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13522 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13631 (p : Pattern) (selected : d13528 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13510 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13627 q selected
    | true =>
      simp only [d13510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13511 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13523 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13630 q selected
    | true =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13524 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13525 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13526 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13527 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13528 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13632 (p : Pattern) (selected : d13530 p = 2) : d13482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1915 q = 2) : d1857 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1915, d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
  have h2 (q : Pattern) (selected : d1726 q = 2) : d1555 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro957 q selected
    | true =>
      simp only [d1726, d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1916 q = 2) : d1858 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1916, d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1727 q = 2) : d1556 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1727, d1556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1917 q = 2) : d1859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1917, d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1917, d1859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1918 q = 2) : d1860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1918, d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1918, d1860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1919 q = 2) : d1862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
  have h8 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1920 q = 2) : d1863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1921 q = 2) : d1864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1922 q = 2) : d1865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1923 q = 2) : d1866 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1923, d1866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1923, d1866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13530 q = 2) : d13482 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13530, d13482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13530, d13482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13633 (p : Pattern) (selected : d13531 p = 2) : d6495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1919 q = 2) : d1862 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
  have h2 (q : Pattern) (selected : d1741 q = 2) : d1570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro960 q selected
    | true =>
      simp only [d1741, d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 2) : d1863 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 2) : d1571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, d1571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 2) : d1864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, d1864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1922 q = 2) : d1865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, d1865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1924 q = 2) : d1868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
  have h8 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1925 q = 2) : d1869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1926 q = 2) : d1870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1927 q = 2) : d1871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1928 q = 2) : d1872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1928, d1872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1928, d1872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13531 q = 2) : d6495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13531, d6495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13531, d6495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13634 (p : Pattern) (selected : d13540 p = 2) : d6501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13535 q = 2) : d6496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13535, d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
  have h2 (q : Pattern) (selected : d10243 q = 2) : d5134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10624 q selected
    | true =>
      simp only [d10243, d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13536 q = 2) : d6497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13536, d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10245 q = 2) : d5135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10245, d5135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13537 q = 2) : d6498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13537, d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13537, d6498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13538 q = 2) : d6499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13538, d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13538, d6499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13539 q = 2) : d6500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13539, d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13539, d6500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13540 q = 2) : d6501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13540, d6501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13540, d6501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13635 (p : Pattern) (selected : d13545 p = 2) : d13516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1924 q = 2) : d1868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d1868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
  have h2 (q : Pattern) (selected : d1753 q = 2) : d1582 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro961 q selected
    | true =>
      simp only [d1753, d1582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 2) : d1869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, d1869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 2) : d1583 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, d1583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 2) : d1870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, d1870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1927 q = 2) : d1871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, d1871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1930 q = 2) : d1877 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1930, d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1930, d1877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13545 q = 2) : d13516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13545, d13516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13545, d13516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13636 (p : Pattern) (selected : d13551 p = 2) : d13569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13532 q = 2) : d13500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13532, d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13632 q selected
    | true =>
      simp only [d13532, d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13633 q selected
  have h2 (q : Pattern) (selected : d13533 q = 2) : d13501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13533, d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13533, d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13534 q = 2) : d13502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13534, d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13534, d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13541 q = 2) : d6502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13541, d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13633 q selected
    | true =>
      simp only [d13541, d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13634 q selected
  have h5 (q : Pattern) (selected : d13542 q = 2) : d6503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13542, d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13542, d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13543 q = 2) : d6504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13543, d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13543, d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13544 q = 2) : d13503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13544, d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13544, d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13546 q = 2) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13546, d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13633 q selected
    | true =>
      simp only [d13546, d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13635 q selected
  have h9 (q : Pattern) (selected : d13547 q = 2) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13547, d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13547, d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13548 q = 2) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13548, d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13548, d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13549 q = 2) : d13520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13549, d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13549, d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13550 q = 2) : d13568 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13550, d13568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13550, d13568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13551 q = 2) : d13569 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13551, d13569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13551, d13569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13637 (p : Pattern) (selected : d13555 p = 2) : d13522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13546 q = 2) : d13517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13546, d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13633 q selected
    | true =>
      simp only [d13546, d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13635 q selected
  have h2 (q : Pattern) (selected : d13547 q = 2) : d13518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13547, d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13547, d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13548 q = 2) : d13519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13548, d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13548, d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13549 q = 2) : d13520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13549, d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13549, d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13554 q = 2) : d13521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13554, d13521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13554, d13521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13555 q = 2) : d13522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13555, d13522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13555, d13522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13638 (p : Pattern) (selected : d13561 p = 2) : d150451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13552 q = 2) : d13570 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13552, d13570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13636 q selected
    | true =>
      simp only [d13552, d13570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13553 q = 2) : d13571 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13553, d13571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13553, d13571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13556 q = 2) : d13523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13556, d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13637 q selected
    | true =>
      simp only [d13556, d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13557 q = 2) : d13524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13557, d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13557, d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13558 q = 2) : d150448 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13558, d150448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13558, d150448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13559 q = 2) : d150449 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13559, d150449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13559, d150449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13560 q = 2) : d150450 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13560, d150450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13560, d150450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13561 q = 2) : d150451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13561, d150451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13561, d150451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13639 (p : Pattern) (selected : d13565 p = 2) : d13586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13556 q = 2) : d13523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13556, d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13637 q selected
    | true =>
      simp only [d13556, d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13557 q = 2) : d13524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13557, d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13557, d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13562 q = 2) : d13583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13562, d13583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13562, d13583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13563 q = 2) : d13584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13563, d13584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13563, d13584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13564 q = 2) : d13585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13564, d13585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13564, d13585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13565 q = 2) : d13586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13565, d13586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13565, d13586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13640 (p : Pattern) (selected : d13569 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13500 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13624 q selected
    | true =>
      simp only [d13500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
  have h2 (q : Pattern) (selected : d13501 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13502 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6502 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d6502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4565 q selected
  have h5 (q : Pattern) (selected : d6503 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6504 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13503 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13517 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4564 q selected
    | true =>
      simp only [d13517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13629 q selected
  have h9 (q : Pattern) (selected : d13518 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13519 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13520 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13568 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13569 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13641 (p : Pattern) (selected : d13575 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13570 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13640 q selected
    | true =>
      simp only [d13570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13571 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13572 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13573 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13574 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13575 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13642 (p : Pattern) (selected : d13581 p = 2) : d150457 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13529 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13628 q selected
    | true =>
      simp only [d13529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13631 q selected
  have h2 (q : Pattern) (selected : d13566 q = 2) : d150452 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13566, d150452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13638 q selected
    | true =>
      simp only [d13566, d150452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13639 q selected
  have h3 (q : Pattern) (selected : d13567 q = 2) : d150453 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13567, d150453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13567, d150453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13576 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13641 q selected
    | true =>
      simp only [d13576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13577 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13578 q = 2) : d150454 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13578, d150454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13578, d150454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13579 q = 2) : d150455 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13579, d150455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13579, d150455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13580 q = 2) : d150456 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13580, d150456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13580, d150456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13581 q = 2) : d150457 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13581, d150457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13581, d150457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13643 (p : Pattern) (selected : d13586 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13523 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13630 q selected
    | true =>
      simp only [d13523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13524 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13583 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13584 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13585 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13586 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13644 (p : Pattern) (selected : d13592 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13587 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13643 q selected
    | true =>
      simp only [d13587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13588 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13589 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13590 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13591 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13592 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13645 (p : Pattern) (selected : d13598 p = 2) : d150463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13314 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13584 q selected
  have h2 (q : Pattern) (selected : d13315 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13324 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13584 q selected
    | true =>
      simp only [d13324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13587 q selected
  have h4 (q : Pattern) (selected : d13325 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13326 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13449 q = 2) : d13324 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13449, d13324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13608 q selected
    | true =>
      simp only [d13449, d13324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13618 q selected
  have h7 (q : Pattern) (selected : d13467 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13619 q selected
    | true =>
      simp only [d13467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13620 q selected
  have h8 (q : Pattern) (selected : d13468 q = 2) : d13325 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13468, d13325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13468, d13325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13469 q = 2) : d150440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13469, d150440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13469, d150440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13470 q = 2) : d150441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13470, d150441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13470, d150441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13474 q = 2) : d150443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13474, d150443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13474, d150443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13621 q selected
  have h12 (q : Pattern) (selected : d13476 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13622 q selected
  have h13 (q : Pattern) (selected : d13477 q = 2) : d150444 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13477, d150444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13477, d150444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13478 q = 2) : d150445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13478, d150445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13478, d150445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d13479 q = 2) : d150446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13479, d150446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d13479, d150446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d13480 q = 2) : d150447 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13480, d150447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13480, d150447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d13582 q = 2) : d150458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13582, d150458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13582, d150458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13642 q selected
  have h18 (q : Pattern) (selected : d13593 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13644 q selected
  have h19 (q : Pattern) (selected : d13594 q = 2) : d150459 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13594, d150459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13594, d150459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13595 q = 2) : d150460 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13595, d150460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13595, d150460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d13596 q = 2) : d150461 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13596, d150461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d13596, d150461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d13597 q = 2) : d150462 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13597, d150462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13597, d150462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13598 q = 2) : d150463 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d13598, d150463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d13598, d150463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13646 (p : Pattern) (selected : d13604 p = 2) : d150469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13599 q = 2) : d150464 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d13599, d150464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13599, d150464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13645 q selected
  have h2 (q : Pattern) (selected : d13600 q = 2) : d150465 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d13600, d150465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13600, d150465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13601 q = 2) : d150466 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d13601, d150466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13601, d150466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13602 q = 2) : d150467 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d13602, d150467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13602, d150467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13603 q = 2) : d150468 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d13603, d150468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13603, d150468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13604 q = 2) : d150469 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d13604, d150469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13604, d150469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13647 (p : Pattern) (selected : d13609 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2037 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2038 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2053 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2054 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2055 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2056 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2057 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13609 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13648 (p : Pattern) (selected : d13614 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2067 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2068 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2071 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13614 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13649 (p : Pattern) (selected : d13620 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13610 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13647 q selected
    | true =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
  have h2 (q : Pattern) (selected : d13611 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13612 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5253 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
    | true =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3873 q selected
  have h5 (q : Pattern) (selected : d5254 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5255 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13613 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13615 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
    | true =>
      simp only [d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13648 q selected
  have h9 (q : Pattern) (selected : d13616 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13617 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13618 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13619 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13620 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13650 (p : Pattern) (selected : d13624 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13615 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
    | true =>
      simp only [d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13648 q selected
  have h2 (q : Pattern) (selected : d13616 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13617 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13618 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13623 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13624 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13651 (p : Pattern) (selected : d13630 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13628 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13629 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13630 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13652 (p : Pattern) (selected : d13634 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13633 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13634 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13653 (p : Pattern) (selected : d13640 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13635 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13651 q selected
    | true =>
      simp only [d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13652 q selected
  have h2 (q : Pattern) (selected : d13636 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13637 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13638 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13639 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13640 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13654 (p : Pattern) (selected : d13643 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13628 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13629 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13643 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13655 (p : Pattern) (selected : d13644 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13633 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13644 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13656 (p : Pattern) (selected : d13650 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13635 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13651 q selected
    | true =>
      simp only [d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13652 q selected
  have h2 (q : Pattern) (selected : d13636 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13637 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13638 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13639 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13645 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13654 q selected
    | true =>
      simp only [d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13655 q selected
  have h7 (q : Pattern) (selected : d13646 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13647 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13648 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13649 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13650 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13657 (p : Pattern) (selected : d13655 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13628 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13654 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13655 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13658 (p : Pattern) (selected : d13657 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13656 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13657 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13659 (p : Pattern) (selected : d13664 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13662 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13663 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13664 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13660 (p : Pattern) (selected : d13667 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13665 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13666 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13667 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13661 (p : Pattern) (selected : d13671 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2144 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2145 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2146 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2147 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2037 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2038 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2148 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13671 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13662 (p : Pattern) (selected : d13677 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1007 q selected
    | true =>
      simp only [d2020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1008 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d2024 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1009 q selected
  have h3 (q : Pattern) (selected : d2025 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5715 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d5715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d5716 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d5716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d5717 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d13677 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d13677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro13663 (p : Pattern) (selected : d13683 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13675 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13676 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13678 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13662 q selected
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13679 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13680 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13681 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13682 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13683 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13664 (p : Pattern) (selected : d13689 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13672 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13661 q selected
    | true =>
      simp only [d13672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13647 q selected
  have h2 (q : Pattern) (selected : d13673 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13674 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13684 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13647 q selected
    | true =>
      simp only [d13684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13663 q selected
  have h5 (q : Pattern) (selected : d13685 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13686 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13687 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13610 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13647 q selected
    | true =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
  have h9 (q : Pattern) (selected : d13611 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13612 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d5253 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
    | true =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3873 q selected
  have h12 (q : Pattern) (selected : d5254 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d5255 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13613 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13688 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13689 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13665 (p : Pattern) (selected : d13693 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13610 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13647 q selected
    | true =>
      simp only [d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
  have h2 (q : Pattern) (selected : d13611 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13612 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d5253 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3871 q selected
    | true =>
      simp only [d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3873 q selected
  have h5 (q : Pattern) (selected : d5254 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d5255 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13613 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d5256 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d5256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13692 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13693 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13666 (p : Pattern) (selected : d13699 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13690 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13664 q selected
    | true =>
      simp only [d13690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13691 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13694 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13665 q selected
    | true =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13695 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13696 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13697 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13698 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13699 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13667 (p : Pattern) (selected : d13703 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13694 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13665 q selected
    | true =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13695 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13700 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13701 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13702 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13703 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13668 (p : Pattern) (selected : d13705 p = 2) : d13609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2201 q = 2) : d2035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
    | true =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 2) : d2036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2203 q = 2) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2203, d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2203, d2037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2204 q = 2) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2204, d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2204, d2038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2221 q = 2) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2222 q = 2) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2223 q = 2) : d2057 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2223, d2057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2223, d2057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13705 q = 2) : d13609 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13705, d13609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13705, d13609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13669 (p : Pattern) (selected : d13706 p = 2) : d5237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 2) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, d2055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2222 q = 2) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, d2056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2233 q = 2) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2234 q = 2) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2235 q = 2) : d2069 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2235, d2069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2235, d2069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13706 q = 2) : d5237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13706, d5237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13706, d5237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13670 (p : Pattern) (selected : d13713 p = 2) : d5252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d10508 q = 2) : d5247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
    | true =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 2) : d5248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13710 q = 2) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13710, d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13710, d5249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13711 q = 2) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13711, d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13711, d5250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13712 q = 2) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13712, d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13712, d5251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13713 q = 2) : d5252 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13713, d5252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13713, d5252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13671 (p : Pattern) (selected : d13718 p = 2) : d13614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 2) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d2067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2234 q = 2) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, d2068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2237 q = 2) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2237, d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2237, d2071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13718 q = 2) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13718, d13614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13718, d13614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13672 (p : Pattern) (selected : d13724 p = 2) : d13620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13707 q = 2) : d13610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13707, d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13668 q selected
    | true =>
      simp only [d13707, d13610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13669 q selected
  have h2 (q : Pattern) (selected : d13708 q = 2) : d13611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13708, d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13708, d13611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13709 q = 2) : d13612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13709, d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13709, d13612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13714 q = 2) : d5253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13714, d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13669 q selected
    | true =>
      simp only [d13714, d5253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13670 q selected
  have h5 (q : Pattern) (selected : d13715 q = 2) : d5254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13715, d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13715, d5254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13716 q = 2) : d5255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13716, d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13716, d5255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13717 q = 2) : d13613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13717, d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13717, d13613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13719 q = 2) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13719, d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13669 q selected
    | true =>
      simp only [d13719, d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13671 q selected
  have h9 (q : Pattern) (selected : d13720 q = 2) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13720, d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13720, d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13721 q = 2) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13721, d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13721, d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13722 q = 2) : d13618 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13722, d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13722, d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13723 q = 2) : d13619 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13723, d13619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13723, d13619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13724 q = 2) : d13620 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13724, d13620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13724, d13620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13673 (p : Pattern) (selected : d13728 p = 2) : d13624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13719 q = 2) : d13615 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13719, d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13669 q selected
    | true =>
      simp only [d13719, d13615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13671 q selected
  have h2 (q : Pattern) (selected : d13720 q = 2) : d13616 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13720, d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13720, d13616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13721 q = 2) : d13617 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13721, d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13721, d13617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13722 q = 2) : d13618 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13722, d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13722, d13618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13727 q = 2) : d13623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13727, d13623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13727, d13623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13728 q = 2) : d13624 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13728, d13624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13728, d13624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13674 (p : Pattern) (selected : d13734 p = 2) : d13630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13725 q = 2) : d13621 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13725, d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13672 q selected
    | true =>
      simp only [d13725, d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13726 q = 2) : d13622 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13726, d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13726, d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13729 q = 2) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13673 q selected
    | true =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13730 q = 2) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13731 q = 2) : d13627 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13731, d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13731, d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13732 q = 2) : d13628 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13732, d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13732, d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13733 q = 2) : d13629 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13733, d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13733, d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13734 q = 2) : d13630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13734, d13630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13734, d13630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13675 (p : Pattern) (selected : d13738 p = 2) : d13634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13729 q = 2) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13673 q selected
    | true =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13730 q = 2) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13735 q = 2) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13735, d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13735, d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13736 q = 2) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13736, d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13736, d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13737 q = 2) : d13633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13737, d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13737, d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13738 q = 2) : d13634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13738, d13634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13738, d13634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13676 (p : Pattern) (selected : d13744 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13741 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13742 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13743 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13744 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13677 (p : Pattern) (selected : d13750 p = 2) : d13640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13658 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13657 q selected
    | true =>
      simp only [d13658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13658 q selected
  have h2 (q : Pattern) (selected : d13659 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13660 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13661 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13668 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13659 q selected
    | true =>
      simp only [d13668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13660 q selected
  have h6 (q : Pattern) (selected : d13669 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13670 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13704 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13666 q selected
    | true =>
      simp only [d13704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13667 q selected
  have h9 (q : Pattern) (selected : d13739 q = 2) : d13635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13739, d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13674 q selected
    | true =>
      simp only [d13739, d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13675 q selected
  have h10 (q : Pattern) (selected : d13740 q = 2) : d13636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13740, d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13740, d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13745 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13676 q selected
    | true =>
      simp only [d13745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13746 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13747 q = 2) : d13637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13747, d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13747, d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13748 q = 2) : d13638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13748, d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13748, d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13749 q = 2) : d13639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13749, d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13749, d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13750 q = 2) : d13640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13750, d13640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13750, d13640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro13678 (p : Pattern) (selected : d13751 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13628 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13654 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13751 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13679 (p : Pattern) (selected : d13752 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13632 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13656 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13752 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13680 (p : Pattern) (selected : d13757 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13627 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13662 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13663 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13757 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13681 (p : Pattern) (selected : d13758 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13631 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13665 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13666 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13758 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13682 (p : Pattern) (selected : d13762 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13690 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13664 q selected
    | true =>
      simp only [d13690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13691 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13694 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13665 q selected
    | true =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13695 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13696 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13697 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13698 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13762 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13683 (p : Pattern) (selected : d13763 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13694 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13665 q selected
    | true =>
      simp only [d13694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13695 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13625 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13650 q selected
    | true =>
      simp only [d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13626 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13700 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13701 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13702 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13763 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13684 (p : Pattern) (selected : d13765 p = 2) : d13643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13725 q = 2) : d13621 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13725, d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13672 q selected
    | true =>
      simp only [d13725, d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13726 q = 2) : d13622 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13726, d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13726, d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13729 q = 2) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13673 q selected
    | true =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13730 q = 2) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13731 q = 2) : d13627 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13731, d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13731, d13627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13732 q = 2) : d13628 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13732, d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13732, d13628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13733 q = 2) : d13629 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13733, d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13733, d13629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13765 q = 2) : d13643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13765, d13643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13765, d13643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13685 (p : Pattern) (selected : d13766 p = 2) : d13644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13729 q = 2) : d13625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13673 q selected
    | true =>
      simp only [d13729, d13625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13730 q = 2) : d13626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13730, d13626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13735 q = 2) : d13631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13735, d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13735, d13631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13736 q = 2) : d13632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13736, d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13736, d13632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13737 q = 2) : d13633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13737, d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13737, d13633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13766 q = 2) : d13644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13766, d13644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13766, d13644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13686 (p : Pattern) (selected : d13769 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13621 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13649 q selected
    | true =>
      simp only [d13621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13622 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13741 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13742 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13743 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13769 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13687 (p : Pattern) (selected : d13775 p = 2) : d13650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13658 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13657 q selected
    | true =>
      simp only [d13658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13658 q selected
  have h2 (q : Pattern) (selected : d13659 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13660 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13661 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13668 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13659 q selected
    | true =>
      simp only [d13668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13660 q selected
  have h6 (q : Pattern) (selected : d13669 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13670 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13704 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13666 q selected
    | true =>
      simp only [d13704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13667 q selected
  have h9 (q : Pattern) (selected : d13739 q = 2) : d13635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13739, d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13674 q selected
    | true =>
      simp only [d13739, d13635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13675 q selected
  have h10 (q : Pattern) (selected : d13740 q = 2) : d13636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13740, d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13740, d13636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13745 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13676 q selected
    | true =>
      simp only [d13745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13746 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13747 q = 2) : d13637 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13747, d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13747, d13637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13748 q = 2) : d13638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13748, d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13748, d13638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13749 q = 2) : d13639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13749, d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13749, d13639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13753 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13678 q selected
    | true =>
      simp only [d13753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13679 q selected
  have h17 (q : Pattern) (selected : d13754 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d13755 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d13756 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13759 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13680 q selected
    | true =>
      simp only [d13759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13681 q selected
  have h21 (q : Pattern) (selected : d13760 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d13761 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13764 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13682 q selected
    | true =>
      simp only [d13764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13683 q selected
  have h24 (q : Pattern) (selected : d13767 q = 2) : d13645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13767, d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13684 q selected
    | true =>
      simp only [d13767, d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13685 q selected
  have h25 (q : Pattern) (selected : d13768 q = 2) : d13646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13768, d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d13768, d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d13770 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13686 q selected
    | true =>
      simp only [d13770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d13771 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d13771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d13772 q = 2) : d13647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13772, d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d13772, d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d13773 q = 2) : d13648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13773, d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d13773, d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d13774 q = 2) : d13649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13774, d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13774, d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d13775 q = 2) : d13650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13775, d13650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13775, d13650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro13688 (p : Pattern) (selected : d13787 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13777 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13667 q selected
    | true =>
      simp only [d13777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13652 q selected
  have h2 (q : Pattern) (selected : d13778 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13779 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13780 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13781 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13782 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13652 q selected
    | true =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13783 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13784 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13785 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13786 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13787 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13689 (p : Pattern) (selected : d13793 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13782 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13652 q selected
    | true =>
      simp only [d13782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13783 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13784 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13785 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13786 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13788 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13655 q selected
    | true =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13789 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13790 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13791 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13792 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13793 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13690 (p : Pattern) (selected : d13800 p = 2) : d150476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13764 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13682 q selected
    | true =>
      simp only [d13764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13683 q selected
  have h2 (q : Pattern) (selected : d13767 q = 2) : d13645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13767, d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13684 q selected
    | true =>
      simp only [d13767, d13645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13685 q selected
  have h3 (q : Pattern) (selected : d13768 q = 2) : d13646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13768, d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13768, d13646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13770 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13686 q selected
    | true =>
      simp only [d13770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13771 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13772 q = 2) : d13647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13772, d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13772, d13647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13798 q = 2) : d13648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13798, d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13798, d13648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13799 q = 2) : d13649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13799, d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13799, d13649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13800 q = 2) : d150476 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13800, d150476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13800, d150476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13691 (p : Pattern) (selected : d13802 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13788 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13655 q selected
    | true =>
      simp only [d13788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13789 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13790 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13791 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13792 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13802 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13692 (p : Pattern) (selected : d13808 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2331 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
  have h2 (q : Pattern) (selected : d2144 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1034 q selected
    | true =>
      simp only [d2144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2332 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2145 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2333 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2334 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2335 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
  have h8 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2336 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2337 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2338 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2339 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13808 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13693 (p : Pattern) (selected : d13809 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2335 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
  have h2 (q : Pattern) (selected : d2035 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1011 q selected
    | true =>
      simp only [d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2036 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2337 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2338 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2340 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
  have h8 (q : Pattern) (selected : d2053 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1016 q selected
    | true =>
      simp only [d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2341 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2054 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2342 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2343 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2344 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13809 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13694 (p : Pattern) (selected : d13822 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13813 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
  have h2 (q : Pattern) (selected : d10353 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10641 q selected
    | true =>
      simp only [d10353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13814 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10355 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13815 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13816 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13817 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13662 q selected
  have h8 (q : Pattern) (selected : d13678 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13662 q selected
    | true =>
      simp only [d13678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13818 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13679 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13819 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d13820 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13821 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13822 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13695 (p : Pattern) (selected : d13832 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13810 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13692 q selected
    | true =>
      simp only [d13810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13693 q selected
  have h2 (q : Pattern) (selected : d13811 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13812 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13823 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13693 q selected
    | true =>
      simp only [d13823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13694 q selected
  have h5 (q : Pattern) (selected : d13824 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13825 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13826 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13827 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13693 q selected
    | true =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
  have h9 (q : Pattern) (selected : d13828 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13829 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d6649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4592 q selected
  have h12 (q : Pattern) (selected : d6650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d6651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13830 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13831 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13832 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro13696 (p : Pattern) (selected : d13836 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13827 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13693 q selected
    | true =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
  have h2 (q : Pattern) (selected : d13828 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13829 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4592 q selected
  have h5 (q : Pattern) (selected : d6650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13830 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d6652 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d6652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13835 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13836 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13697 (p : Pattern) (selected : d13842 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13833 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13695 q selected
    | true =>
      simp only [d13833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13834 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13837 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13696 q selected
    | true =>
      simp only [d13837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13838 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13839 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13840 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13841 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13842 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13698 (p : Pattern) (selected : d13843 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2346 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
  have h2 (q : Pattern) (selected : d2065 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1017 q selected
    | true =>
      simp only [d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2349 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2355 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13843 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13699 (p : Pattern) (selected : d13849 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13844 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13698 q selected
  have h2 (q : Pattern) (selected : d13845 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13846 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13847 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13848 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13849 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13700 (p : Pattern) (selected : d13855 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13837 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13696 q selected
    | true =>
      simp only [d13837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13838 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13850 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13699 q selected
    | true =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13851 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13852 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13853 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13854 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13855 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13701 (p : Pattern) (selected : d13857 p = 2) : d13809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2393 q = 2) : d2335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2393, d2335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
  have h2 (q : Pattern) (selected : d2201 q = 2) : d2035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1045 q selected
    | true =>
      simp only [d2201, d2035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2394 q = 2) : d2336 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2394, d2336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2202 q = 2) : d2036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2202, d2036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2395 q = 2) : d2337 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2395, d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2395, d2337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2396 q = 2) : d2338 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2396, d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2396, d2338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2397 q = 2) : d2340 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
  have h8 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2398 q = 2) : d2341 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2399 q = 2) : d2342 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2400 q = 2) : d2343 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2401 q = 2) : d2344 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2401, d2344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2401, d2344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13857 q = 2) : d13809 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13857, d13809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13857, d13809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13702 (p : Pattern) (selected : d13858 p = 2) : d6642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2397 q = 2) : d2340 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d2340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
  have h2 (q : Pattern) (selected : d2219 q = 2) : d2053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1050 q selected
    | true =>
      simp only [d2219, d2053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 2) : d2341 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d2341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 2) : d2054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, d2054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 2) : d2342 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, d2342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2400 q = 2) : d2343 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2400, d2343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2402 q = 2) : d2346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
  have h8 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2403 q = 2) : d2347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2404 q = 2) : d2348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2405 q = 2) : d2349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2406 q = 2) : d2350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2406, d2350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2406, d2350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13858 q = 2) : d6642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13858, d6642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13858, d6642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro13703 (p : Pattern) (selected : d13867 p = 2) : d6648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13862 q = 2) : d6643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13862, d6643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
  have h2 (q : Pattern) (selected : d10508 q = 2) : d5247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10663 q selected
    | true =>
      simp only [d10508, d5247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13863 q = 2) : d6644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13863, d6644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10510 q = 2) : d5248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10510, d5248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13864 q = 2) : d6645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13864, d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13864, d6645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13865 q = 2) : d6646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13865, d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13865, d6646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13866 q = 2) : d6647 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13866, d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13866, d6647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13867 q = 2) : d6648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13867, d6648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13867, d6648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13704 (p : Pattern) (selected : d13872 p = 2) : d13843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2402 q = 2) : d2346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d2346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
  have h2 (q : Pattern) (selected : d2231 q = 2) : d2065 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1051 q selected
    | true =>
      simp only [d2231, d2065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 2) : d2347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d2347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 2) : d2066 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, d2066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 2) : d2348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, d2348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2405 q = 2) : d2349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2405, d2349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2408 q = 2) : d2355 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2408, d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2408, d2355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13872 q = 2) : d13843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13872, d13843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13872, d13843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13705 (p : Pattern) (selected : d13878 p = 2) : d13896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13859 q = 2) : d13827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13859, d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13701 q selected
    | true =>
      simp only [d13859, d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13702 q selected
  have h2 (q : Pattern) (selected : d13860 q = 2) : d13828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13860, d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13860, d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13861 q = 2) : d13829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13861, d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13861, d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13868 q = 2) : d6649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13868, d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13702 q selected
    | true =>
      simp only [d13868, d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13703 q selected
  have h5 (q : Pattern) (selected : d13869 q = 2) : d6650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13869, d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13869, d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13870 q = 2) : d6651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13870, d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13870, d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13871 q = 2) : d13830 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13871, d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13871, d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13873 q = 2) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13873, d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13702 q selected
    | true =>
      simp only [d13873, d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13704 q selected
  have h9 (q : Pattern) (selected : d13874 q = 2) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13874, d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13874, d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13875 q = 2) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13875, d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13875, d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13876 q = 2) : d13847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13876, d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13876, d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13877 q = 2) : d13895 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13877, d13895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13877, d13895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13878 q = 2) : d13896 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13878, d13896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13878, d13896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13706 (p : Pattern) (selected : d13882 p = 2) : d13849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13873 q = 2) : d13844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13873, d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13702 q selected
    | true =>
      simp only [d13873, d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13704 q selected
  have h2 (q : Pattern) (selected : d13874 q = 2) : d13845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13874, d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13874, d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13875 q = 2) : d13846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13875, d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13875, d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13876 q = 2) : d13847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13876, d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13876, d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13881 q = 2) : d13848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13881, d13848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13881, d13848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13882 q = 2) : d13849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13882, d13849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13882, d13849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13707 (p : Pattern) (selected : d13888 p = 2) : d150485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13879 q = 2) : d13897 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13879, d13897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13705 q selected
    | true =>
      simp only [d13879, d13897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13880 q = 2) : d13898 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13880, d13898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13880, d13898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13883 q = 2) : d13850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13883, d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13706 q selected
    | true =>
      simp only [d13883, d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13884 q = 2) : d13851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13884, d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13884, d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13885 q = 2) : d150482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13885, d150482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13885, d150482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13886 q = 2) : d150483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13886, d150483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13886, d150483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13887 q = 2) : d150484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13887, d150484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13887, d150484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13888 q = 2) : d150485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13888, d150485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13888, d150485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13708 (p : Pattern) (selected : d13892 p = 2) : d13913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13883 q = 2) : d13850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13883, d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13706 q selected
    | true =>
      simp only [d13883, d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13884 q = 2) : d13851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13884, d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13884, d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13889 q = 2) : d13910 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13889, d13910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13889, d13910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13890 q = 2) : d13911 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13890, d13911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13890, d13911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13891 q = 2) : d13912 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13891, d13912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13891, d13912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13892 q = 2) : d13913 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13892, d13913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13892, d13913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13709 (p : Pattern) (selected : d13896 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13827 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13693 q selected
    | true =>
      simp only [d13827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
  have h2 (q : Pattern) (selected : d13828 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13829 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d6649 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d6649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4592 q selected
  have h5 (q : Pattern) (selected : d6650 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d6651 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13830 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13844 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4591 q selected
    | true =>
      simp only [d13844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13698 q selected
  have h9 (q : Pattern) (selected : d13845 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13846 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13847 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d13895 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13896 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d13896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro13710 (p : Pattern) (selected : d13902 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13897 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13709 q selected
    | true =>
      simp only [d13897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13898 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13899 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13900 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13901 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13902 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13711 (p : Pattern) (selected : d13908 p = 2) : d150491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13856 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13697 q selected
    | true =>
      simp only [d13856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13700 q selected
  have h2 (q : Pattern) (selected : d13893 q = 2) : d150486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13893, d150486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13707 q selected
    | true =>
      simp only [d13893, d150486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13708 q selected
  have h3 (q : Pattern) (selected : d13894 q = 2) : d150487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13894, d150487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13894, d150487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13903 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13710 q selected
    | true =>
      simp only [d13903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13904 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13905 q = 2) : d150488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13905, d150488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13905, d150488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13906 q = 2) : d150489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13906, d150489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13906, d150489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d13907 q = 2) : d150490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13907, d150490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13907, d150490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13908 q = 2) : d150491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13908, d150491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13908, d150491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro13712 (p : Pattern) (selected : d13913 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13850 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13699 q selected
    | true =>
      simp only [d13850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13851 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13910 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13911 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13912 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13913 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13713 (p : Pattern) (selected : d13919 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13914 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13712 q selected
    | true =>
      simp only [d13914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13915 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13916 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13917 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13918 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13919 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13714 (p : Pattern) (selected : d13925 p = 2) : d150497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13641 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13653 q selected
  have h2 (q : Pattern) (selected : d13642 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13651 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13653 q selected
    | true =>
      simp only [d13651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13656 q selected
  have h4 (q : Pattern) (selected : d13652 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13653 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13776 q = 2) : d13651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13776, d13651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13677 q selected
    | true =>
      simp only [d13776, d13651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13687 q selected
  have h7 (q : Pattern) (selected : d13794 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13688 q selected
    | true =>
      simp only [d13794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13689 q selected
  have h8 (q : Pattern) (selected : d13795 q = 2) : d13652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13795, d13652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13795, d13652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13796 q = 2) : d150474 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13796, d150474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13796, d150474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13797 q = 2) : d150475 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13797, d150475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13797, d150475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13801 q = 2) : d150477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13801, d150477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13801, d150477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13690 q selected
  have h12 (q : Pattern) (selected : d13803 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13691 q selected
  have h13 (q : Pattern) (selected : d13804 q = 2) : d150478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13804, d150478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d13804, d150478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13805 q = 2) : d150479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13805, d150479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d13805, d150479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d13806 q = 2) : d150480 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13806, d150480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d13806, d150480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d13807 q = 2) : d150481 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13807, d150481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13807, d150481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d13909 q = 2) : d150492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13909, d150492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13909, d150492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13711 q selected
  have h18 (q : Pattern) (selected : d13920 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13713 q selected
  have h19 (q : Pattern) (selected : d13921 q = 2) : d150493 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13921, d150493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d13921, d150493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d13922 q = 2) : d150494 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13922, d150494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d13922, d150494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d13923 q = 2) : d150495 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d13923, d150495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d13923, d150495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d13924 q = 2) : d150496 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d13924, d150496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d13924, d150496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d13925 q = 2) : d150497 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d13925, d150497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d13925, d150497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro13715 (p : Pattern) (selected : d13931 p = 2) : d150503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13926 q = 2) : d150498 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d13926, d150498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13926, d150498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13714 q selected
  have h2 (q : Pattern) (selected : d13927 q = 2) : d150499 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d13927, d150499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13927, d150499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13928 q = 2) : d150500 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d13928, d150500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13928, d150500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13929 q = 2) : d150501 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d13929, d150501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13929, d150501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13930 q = 2) : d150502 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d13930, d150502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13930, d150502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13931 q = 2) : d150503 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d13931, d150503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13931, d150503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13716 (p : Pattern) (selected : d13937 p = 2) : d150509 p = 1 := by
  have h0 (q : Pattern) (selected : d12687 q = 2) : d150378 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d12687, d150378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13398 q selected
    | true =>
      simp only [d12687, d150378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13452 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d12954 q = 2) : d150405 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d12954, d150405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12954, d150405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13508 q selected
  have h3 (q : Pattern) (selected : d12955 q = 2) : d150406 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d12955, d150406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12955, d150406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13279 q = 2) : d150437 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d13279, d150437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13279, d150437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13577 q selected
  have h5 (q : Pattern) (selected : d13280 q = 2) : d150438 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d13280, d150438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13280, d150438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13281 q = 2) : d150439 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d13281, d150439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13281, d150439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13605 q = 2) : d150470 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d13605, d150470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13605, d150470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13646 q selected
  have h8 (q : Pattern) (selected : d13606 q = 2) : d150471 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d13606, d150471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13606, d150471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d13607 q = 2) : d150472 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d13607, d150472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13607, d150472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13608 q = 2) : d150473 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d13608, d150473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13608, d150473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13932 q = 2) : d150504 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d13932, d150504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13932, d150504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13715 q selected
  have h12 (q : Pattern) (selected : d13933 q = 2) : d150505 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d13933, d150505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13933, d150505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13934 q = 2) : d150506 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d13934, d150506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13934, d150506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13935 q = 2) : d150507 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d13935, d150507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13935, d150507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13936 q = 2) : d150508 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d13936, d150508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13936, d150508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13937 q = 2) : d150509 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d13937, d150509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d13937, d150509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro13717 (p : Pattern) (selected : d13943 p = 2) : d150515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13938 q = 2) : d150510 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d13938, d150510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13716 q selected
    | true =>
      simp only [d13938, d150510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13939 q = 2) : d150511 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d13939, d150511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13939, d150511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13940 q = 2) : d150512 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d13940, d150512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13940, d150512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13941 q = 2) : d150513 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d13941, d150513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13941, d150513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13942 q = 2) : d150514 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d13942, d150514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13942, d150514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13943 q = 2) : d150515 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d13943, d150515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13943, d150515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13718 (p : Pattern) (selected : d13949 p = 2) : d150521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13944 q = 2) : d150516 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d13944, d150516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13717 q selected
    | true =>
      simp only [d13944, d150516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13945 q = 2) : d150517 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d13945, d150517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13945, d150517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13946 q = 2) : d150518 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d13946, d150518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13946, d150518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13947 q = 2) : d150519 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d13947, d150519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13947, d150519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13948 q = 2) : d150520 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d13948, d150520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13948, d150520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13949 q = 2) : d150521 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d13949, d150521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13949, d150521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13719 (p : Pattern) (selected : d13955 p = 2) : d150527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13950 q = 2) : d150522 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d13950, d150522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13718 q selected
    | true =>
      simp only [d13950, d150522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13951 q = 2) : d150523 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d13951, d150523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13951, d150523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13952 q = 2) : d150524 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d13952, d150524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13952, d150524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13953 q = 2) : d150525 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d13953, d150525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13953, d150525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13954 q = 2) : d150526 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d13954, d150526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13954, d150526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13955 q = 2) : d150527 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d13955, d150527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13955, d150527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13720 (p : Pattern) (selected : d13961 p = 2) : d150533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13956 q = 2) : d150528 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d13956, d150528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13719 q selected
    | true =>
      simp only [d13956, d150528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13957 q = 2) : d150529 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d13957, d150529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13957, d150529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13958 q = 2) : d150530 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d13958, d150530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13958, d150530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13959 q = 2) : d150531 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d13959, d150531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13959, d150531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13960 q = 2) : d150532 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d13960, d150532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13960, d150532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13961 q = 2) : d150533 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d13961, d150533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13961, d150533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13721 (p : Pattern) (selected : d13967 p = 2) : d150539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13962 q = 2) : d150534 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d13962, d150534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13720 q selected
    | true =>
      simp only [d13962, d150534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13963 q = 2) : d150535 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d13963, d150535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13963, d150535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13964 q = 2) : d150536 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d13964, d150536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13964, d150536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13965 q = 2) : d150537 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d13965, d150537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13965, d150537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13966 q = 2) : d150538 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d13966, d150538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13966, d150538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13967 q = 2) : d150539 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d13967, d150539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13967, d150539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13722 (p : Pattern) (selected : d13973 p = 2) : d150545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13968 q = 2) : d150540 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d13968, d150540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13721 q selected
    | true =>
      simp only [d13968, d150540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13969 q = 2) : d150541 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d13969, d150541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13969, d150541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13970 q = 2) : d150542 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d13970, d150542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13970, d150542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13971 q = 2) : d150543 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d13971, d150543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13971, d150543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13972 q = 2) : d150544 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d13972, d150544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13972, d150544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13973 q = 2) : d150545 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d13973, d150545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13973, d150545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13723 (p : Pattern) (selected : d13979 p = 2) : d150551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13974 q = 2) : d150546 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d13974, d150546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13722 q selected
    | true =>
      simp only [d13974, d150546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13975 q = 2) : d150547 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d13975, d150547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13975, d150547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13976 q = 2) : d150548 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d13976, d150548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13976, d150548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13977 q = 2) : d150549 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d13977, d150549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13977, d150549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13978 q = 2) : d150550 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d13978, d150550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13978, d150550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13979 q = 2) : d150551 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d13979, d150551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13979, d150551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13724 (p : Pattern) (selected : d152857 p = 0) : d154954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152856 q = 0) : d154953 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d152856, d154953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152856, d154953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152857 q = 0) : d154954 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d152857, d154954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152857, d154954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13725 (p : Pattern) (selected : d152863 p = 0) : d154960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152860 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152861 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152862 q = 0) : d154959 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152863 q = 0) : d154960 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d152863, d154960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152863, d154960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13726 (p : Pattern) (selected : d152869 p = 0) : d154966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152864 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
    | true =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152865 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152866 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152867 q = 0) : d154964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152867, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152867, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152868 q = 0) : d154965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d152868, d154965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152868, d154965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152869 q = 0) : d154966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d152869, d154966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152869, d154966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13727 (p : Pattern) (selected : d152875 p = 0) : d154972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152873 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152874 q = 0) : d154971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152874, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152874, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152875 q = 0) : d154972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152875, d154972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152875, d154972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13728 (p : Pattern) (selected : d152881 p = 0) : d154978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152877 q = 0) : d154974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152878 q = 0) : d154975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152878, d154975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152878, d154975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152879 q = 0) : d154976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152879, d154976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152879, d154976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152880 q = 0) : d154977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152880, d154977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152880, d154977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152881 q = 0) : d154978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152881, d154978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152881, d154978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13729 (p : Pattern) (selected : d152882 p = 0) : d154979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152873 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152874 q = 0) : d154971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152874, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152874, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152882 q = 0) : d154979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152882, d154979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152882, d154979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13730 (p : Pattern) (selected : d152888 p = 0) : d154985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152877 q = 0) : d154974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152878 q = 0) : d154975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152878, d154975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152878, d154975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152879 q = 0) : d154976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152879, d154976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152879, d154976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152880 q = 0) : d154977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152880, d154977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152880, d154977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152884 q = 0) : d154981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152885 q = 0) : d154982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152885, d154982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152885, d154982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152886 q = 0) : d154983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152886, d154983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152886, d154983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152887 q = 0) : d154984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152887, d154984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152887, d154984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152888 q = 0) : d154985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152888, d154985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152888, d154985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13731 (p : Pattern) (selected : d152893 p = 0) : d154990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152884 q = 0) : d154981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152884, d154981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152885 q = 0) : d154982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152885, d154982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152885, d154982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152886 q = 0) : d154983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152886, d154983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152886, d154983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152887 q = 0) : d154984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152887, d154984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152887, d154984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152893 q = 0) : d154990 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152893, d154990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152893, d154990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13732 (p : Pattern) (selected : d152904 p = 0) : d155001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152899 q = 0) : d154996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152899, d154996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
  have h2 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152900 q = 0) : d154997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152900, d154997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152901 q = 0) : d154998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152901, d154998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152902 q = 0) : d154999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152902, d154999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152903 q = 0) : d155000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152903, d155000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152904 q = 0) : d155001 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d152904, d155001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152904, d155001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro13733 (p : Pattern) (selected : d152910 p = 0) : d155007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152905 q = 0) : d155002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13732 q selected
    | true =>
      simp only [d152905, d155002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152906 q = 0) : d155003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152906, d155003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152907 q = 0) : d155004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152907, d155004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152908 q = 0) : d155005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152908, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152908, d155005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152909 q = 0) : d155006 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d152909, d155006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152909, d155006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152910 q = 0) : d155007 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d152910, d155007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152910, d155007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13734 (p : Pattern) (selected : d152916 p = 0) : d155013 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152911 q = 0) : d155008 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152911, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13733 q selected
    | true =>
      simp only [d152911, d155008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152912 q = 0) : d155009 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152912, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152912, d155009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152913 q = 0) : d155010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152913, d155010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152913, d155010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152914 q = 0) : d155011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152914, d155011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152914, d155011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152915 q = 0) : d155012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152915, d155012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152915, d155012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152916 q = 0) : d155013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152916, d155013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152916, d155013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13735 (p : Pattern) (selected : d152922 p = 0) : d155019 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152917 q = 0) : d155014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13734 q selected
    | true =>
      simp only [d152917, d155014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152918 q = 0) : d155015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152918, d155015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152918, d155015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152919 q = 0) : d155016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152919, d155016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152919, d155016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152920 q = 0) : d155017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152920, d155017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152920, d155017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152921 q = 0) : d155018 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152921, d155018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152921, d155018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152922 q = 0) : d155019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152922, d155019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152922, d155019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13736 (p : Pattern) (selected : d152928 p = 0) : d155025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152889 q = 0) : d154986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d152889, d154986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13728 q selected
    | true =>
      simp only [d152889, d154986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13730 q selected
  have h2 (q : Pattern) (selected : d152890 q = 0) : d154987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d152890, d154987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152890, d154987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152891 q = 0) : d154988 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d152891, d154988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152891, d154988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152892 q = 0) : d154989 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d152892, d154989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152892, d154989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152894 q = 0) : d154991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d152894, d154991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152894, d154991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13731 q selected
  have h6 (q : Pattern) (selected : d152895 q = 0) : d154992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d152895, d154992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152895, d154992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152896 q = 0) : d154993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d152896, d154993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152896, d154993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152897 q = 0) : d154994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d152897, d154994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152897, d154994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152898 q = 0) : d154995 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d152898, d154995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152898, d154995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152923 q = 0) : d155020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d152923, d155020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152923, d155020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13735 q selected
  have h11 (q : Pattern) (selected : d152924 q = 0) : d155021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d152924, d155021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d152924, d155021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d152925 q = 0) : d155022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d152925, d155022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d152925, d155022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d152926 q = 0) : d155023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d152926, d155023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d152926, d155023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d152927 q = 0) : d155024 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d152927, d155024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d152927, d155024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d152928 q = 0) : d155025 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d152928, d155025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d152928, d155025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro13737 (p : Pattern) (selected : d152938 p = 0) : d155035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152934 q = 0) : d155031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152935 q = 0) : d155032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152936 q = 0) : d155033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152937 q = 0) : d155034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152938 q = 0) : d155035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152938, d155035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152938, d155035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13738 (p : Pattern) (selected : d152945 p = 0) : d155042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152934 q = 0) : d155031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152934, d155031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152935 q = 0) : d155032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152935, d155032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152936 q = 0) : d155033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152936, d155033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152937 q = 0) : d155034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152937, d155034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152883 q = 0) : d154980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13729 q selected
    | true =>
      simp only [d152883, d154980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152941 q = 0) : d155038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152941, d155038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152941, d155038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152942 q = 0) : d155039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152942, d155039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152942, d155039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152943 q = 0) : d155040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152943, d155040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152943, d155040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152944 q = 0) : d155041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d152944, d155041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152944, d155041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152945 q = 0) : d155042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d152945, d155042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152945, d155042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13739 (p : Pattern) (selected : d152950 p = 0) : d155047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152873 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152873, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152949 q = 0) : d155046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152949, d155046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152949, d155046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152950 q = 0) : d155047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152950, d155047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152950, d155047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13740 (p : Pattern) (selected : d152957 p = 0) : d155054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152872 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152872, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152955 q = 0) : d155052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152955, d155052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152955, d155052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152956 q = 0) : d155053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152956, d155053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152956, d155053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152957 q = 0) : d155054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152957, d155054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152957, d155054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13741 (p : Pattern) (selected : d152962 p = 0) : d155059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152961 q = 0) : d155058 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d152961, d155058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152961, d155058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152962 q = 0) : d155059 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d152962, d155059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152962, d155059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13742 (p : Pattern) (selected : d152968 p = 0) : d155065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152963 q = 0) : d155060 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13741 q selected
    | true =>
      simp only [d152963, d155060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152964 q = 0) : d155061 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152964, d155061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152965 q = 0) : d155062 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152965, d155062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152966 q = 0) : d155063 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152966, d155063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152858 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13724 q selected
    | true =>
      simp only [d152858, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152859 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152859, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152860 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152860, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152861 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152861, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152967 q = 0) : d155064 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152967, d155064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152967, d155064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152862 q = 0) : d154959 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d152862, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d152968 q = 0) : d155065 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d152968, d155065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d152968, d155065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro13743 (p : Pattern) (selected : d152974 p = 0) : d155071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152969 q = 0) : d155066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13742 q selected
    | true =>
      simp only [d152969, d155066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
  have h2 (q : Pattern) (selected : d152970 q = 0) : d155067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152970, d155067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152971 q = 0) : d155068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152971, d155068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152864 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13725 q selected
    | true =>
      simp only [d152864, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152865 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152865, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152866 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152866, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d152972 q = 0) : d155069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152972, d155069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d152867 q = 0) : d154964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152867, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152867, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d152973 q = 0) : d155070 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d152973, d155070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d152973, d155070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d152974 q = 0) : d155071 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d152974, d155071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d152974, d155071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro13744 (p : Pattern) (selected : d152980 p = 0) : d155077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152975 q = 0) : d155072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13743 q selected
    | true =>
      simp only [d152975, d155072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152976 q = 0) : d155073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152976, d155073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152870 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13726 q selected
    | true =>
      simp only [d152870, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152871 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152871, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152977 q = 0) : d155074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152977, d155074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d152978 q = 0) : d155075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152978, d155075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d152979 q = 0) : d155076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d152979, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152979, d155076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152980 q = 0) : d155077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d152980, d155077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152980, d155077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro13745 (p : Pattern) (selected : d152983 p = 0) : d154954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152982 q = 0) : d154953 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d152982, d154953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152982, d154953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152983 q = 0) : d154954 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d152983, d154954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152983, d154954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro13746 (p : Pattern) (selected : d152989 p = 0) : d154960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152984 q = 0) : d154955 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13745 q selected
    | true =>
      simp only [d152984, d154955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152985 q = 0) : d154956 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d152985, d154956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d152986 q = 0) : d154957 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152986, d154957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152987 q = 0) : d154958 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152987, d154958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152988 q = 0) : d154959 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d152988, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152988, d154959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152989 q = 0) : d154960 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d152989, d154960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152989, d154960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13747 (p : Pattern) (selected : d152995 p = 0) : d154966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152990 q = 0) : d154961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d152990, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13746 q selected
    | true =>
      simp only [d152990, d154961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152991 q = 0) : d154962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d152991, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152991, d154962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152992 q = 0) : d154963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d152992, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152992, d154963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d152993 q = 0) : d154964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d152993, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152993, d154964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d152994 q = 0) : d154965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d152994, d154965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d152994, d154965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152995 q = 0) : d154966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d152995, d154966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d152995, d154966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro13748 (p : Pattern) (selected : d153001 p = 0) : d154972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152996 q = 0) : d154967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13747 q selected
    | true =>
      simp only [d152996, d154967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152997 q = 0) : d154968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152997, d154968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152998 q = 0) : d154969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d152998, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152998, d154969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152999 q = 0) : d154970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d152999, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d152999, d154970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d153000 q = 0) : d154971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d153000, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153000, d154971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d153001 q = 0) : d154972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d153001, d154972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153001, d154972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro13749 (p : Pattern) (selected : d153007 p = 0) : d155083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d152951 q = 0) : d155048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152951, d155048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13739 q selected
    | true =>
      simp only [d152951, d155048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152952 q = 0) : d155049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152952, d155049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152952, d155049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d152953 q = 0) : d155050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152953, d155050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d152953, d155050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152954 q = 0) : d155051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d152954, d155051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152954, d155051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d152958 q = 0) : d155055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152958, d155055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13740 q selected
    | true =>
      simp only [d152958, d155055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d152959 q = 0) : d155056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152959, d155056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152959, d155056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d152960 q = 0) : d155057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d152960, d155057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d152960, d155057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d152981 q = 0) : d155078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13744 q selected
    | true =>
      simp only [d152981, d155078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
  have h9 (q : Pattern) (selected : d153002 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d153002, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13748 q selected
    | true =>
      simp only [d153002, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d153003 q = 0) : d155079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d153003, d155079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d153003, d155079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d152876 q = 0) : d154973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro13727 q selected
    | true =>
      simp only [d152876, d154973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d152877 q = 0) : d154974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d152877, d154974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d153004 q = 0) : d155080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d153004, d155080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d153004, d155080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d153005 q = 0) : d155081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d153005, d155081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d153005, d155081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d153006 q = 0) : d155082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d153006, d155082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d153006, d155082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d153007 q = 0) : d155083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d153007, d155083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d153007, d155083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
end NetHack.Soko22Hazard87
