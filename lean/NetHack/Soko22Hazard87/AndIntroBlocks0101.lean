import NetHack.Soko22Hazard87.AndIntroBlocks0100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro25250 (p : Pattern) (ha : d10738 p = 1) (hb : d85724 p = 1) : d88218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d85724 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d85724 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10738 q = 1) (hb : d85724 q = 1) : d88218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25251 (p : Pattern) (ha : d10747 p = 1) (hb : d85723 p = 1) : d88223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10652 q = 1) (hb : d85721 q = 1) : d10652 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10746 q = 1) (hb : d85723 q = 1) : d88222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d85723, d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10746, d85723, d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10747 q = 1) (hb : d85723 q = 1) : d88223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10747, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25252 (p : Pattern) (ha : d10753 p = 1) (hb : d85724 p = 1) : d88229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10748 q = 1) (hb : d85723 q = 1) : d88224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25251 q ha hb
    | true =>
      simp only [d10748, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10749 q = 1) (hb : d85723 q = 1) : d88225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10749, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10656 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d85724 q = 1) : d88226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10750, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d85724 q = 1) : d88227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d85724 q = 1) : d88228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d85724 q = 1) : d88229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25253 (p : Pattern) (ha : d10772 p = 1) (hb : d85724 p = 1) : d88146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10769 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10769, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10770 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10770, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10771 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10771, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10772 q = 1) (hb : d85724 q = 1) : d88146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25254 (p : Pattern) (ha : d85724 p = 1) (hb : d108822 p = 1) : d88235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d85724 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25249 q ha hb
    | true =>
      simp only [d10732, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d85724 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d85724 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d85724 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d85724 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25250 q ha hb
    | true =>
      simp only [d10739, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d85724 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d85724 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d85724 q = 1) : d88230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25252 q ha hb
    | true =>
      simp only [d10754, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108818 q = 1) : d88231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108818, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d10773 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25253 q ha hb
    | true =>
      simp only [d10773, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10774 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10774, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108819 q = 1) : d88232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108819, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108820 q = 1) : d88233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108820, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108821 q = 1) : d88234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108821, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108822 q = 1) : d88235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108822, d88235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25255 (p : Pattern) (ha : d10779 p = 1) (hb : d85724 p = 1) : d88236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d85724 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10779 q = 1) (hb : d85724 q = 1) : d88236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10779, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25256 (p : Pattern) (ha : d10784 p = 1) (hb : d85724 p = 1) : d88241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d85724 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d85724 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10784 q = 1) (hb : d85724 q = 1) : d88241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10784, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25257 (p : Pattern) (ha : d10788 p = 1) (hb : d85724 p = 1) : d88245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d85723 q = 1) : d88224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25251 q ha hb
    | true =>
      simp only [d10748, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d85723 q = 1) : d88225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10656 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10750 q = 1) (hb : d85724 q = 1) : d88226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d85724, d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d85724 q = 1) : d88227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10751, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d85724 q = 1) : d88228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d85724 q = 1) : d88245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25258 (p : Pattern) (ha : d10793 p = 1) (hb : d85724 p = 1) : d88153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10769 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10770 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10770, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10771 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10771, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10793 q = 1) (hb : d85724 q = 1) : d88153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10793, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25259 (p : Pattern) (ha : d85724 p = 1) (hb : d108827 p = 1) : d88251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d85724 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25249 q ha hb
    | true =>
      simp only [d10732, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d85724 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d85724 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d85724 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d85724 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25250 q ha hb
    | true =>
      simp only [d10739, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d85724 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d85724 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d85724 q = 1) : d88230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25252 q ha hb
    | true =>
      simp only [d10754, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108818 q = 1) : d88231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108818, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d10773 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25253 q ha hb
    | true =>
      simp only [d10773, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10774 q = 1) (hb : d85724 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10774, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108819 q = 1) : d88232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108819, d88232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108820 q = 1) : d88233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108820, d88233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108821 q = 1) : d88234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108821, d88234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10780 q = 1) (hb : d85724 q = 1) : d88237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25255 q ha hb
    | true =>
      simp only [d10780, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10279 q ha hb
  have h16 (q : Pattern) (ha : d10781 q = 1) (hb : d85724 q = 1) : d88238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10782 q = 1) (hb : d85724 q = 1) : d88239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10782, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10783 q = 1) (hb : d85724 q = 1) : d88240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10785 q = 1) (hb : d85724 q = 1) : d88242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25256 q ha hb
    | true =>
      simp only [d10785, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10280 q ha hb
  have h20 (q : Pattern) (ha : d10786 q = 1) (hb : d85724 q = 1) : d88243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10787 q = 1) (hb : d85724 q = 1) : d88244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10787, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10789 q = 1) (hb : d85724 q = 1) : d88246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25257 q ha hb
    | true =>
      simp only [d10789, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108823 q = 1) : d88247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108823, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d10794 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25258 q ha hb
    | true =>
      simp only [d10794, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10795 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10795, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108824 q = 1) : d88248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108824, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108825 q = 1) : d88249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108825, d88249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108826 q = 1) : d88250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108826, d88250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108827 q = 1) : d88251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108827, d88251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25260 (p : Pattern) (ha : d85724 p = 1) (hb : d108834 p = 1) : d88260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d85724 q = 1) : d88246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25257 q ha hb
    | true =>
      simp only [d10789, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108823 q = 1) : d88247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108823, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25258 q ha hb
    | true =>
      simp only [d10794, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d85724 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108824 q = 1) : d88248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d88248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108832 q = 1) : d88258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108832, d88258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108833 q = 1) : d88259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108833, d88259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108834 q = 1) : d88260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108834, d88260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25261 (p : Pattern) (ha : d10819 p = 1) (hb : d85723 p = 1) : d88267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10689 q = 1) (hb : d85721 q = 1) : d10689 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10818 q = 1) (hb : d85723 q = 1) : d88266 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d85723, d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10818, d85723, d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10819 q = 1) (hb : d85723 q = 1) : d88267 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10819, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25262 (p : Pattern) (ha : d10825 p = 1) (hb : d85724 p = 1) : d88273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d85723 q = 1) : d88268 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25261 q ha hb
    | true =>
      simp only [d10820, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d85723 q = 1) : d88269 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10693 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10822 q = 1) (hb : d85724 q = 1) : d88270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d85724, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d85724, d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d85724 q = 1) : d88271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10823, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d85724 q = 1) : d88272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d85724 q = 1) : d88273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25263 (p : Pattern) (ha : d10844 p = 1) (hb : d85724 p = 1) : d88177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d85723 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25242 q ha hb
    | true =>
      simp only [d10692, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d85723 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10841 q = 1) (hb : d85724 q = 1) : d88174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10842 q = 1) (hb : d85724 q = 1) : d88175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10842, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10843 q = 1) (hb : d85724 q = 1) : d88176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10843, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10844 q = 1) (hb : d85724 q = 1) : d88177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10844, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25264 (p : Pattern) (ha : d85724 p = 1) (hb : d108844 p = 1) : d88279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d85724 q = 1) : d88274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25262 q ha hb
    | true =>
      simp only [d10826, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25243 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108840 q = 1) : d88275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108840, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25263 q ha hb
    | true =>
      simp only [d10845, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d85724 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108841 q = 1) : d88276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d88276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108842 q = 1) : d88277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108842, d88277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108843 q = 1) : d88278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108843, d88278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108844 q = 1) : d88279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108844, d88279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25265 (p : Pattern) (ha : d85724 p = 1) (hb : d108850 p = 1) : d88285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d85724 q = 1) : d88200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25246 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d85724 q = 1) : d88201 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d85724 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25246 q ha hb
    | true =>
      simp only [d10727, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25247 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d85724 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d85724 q = 1) : d88209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108828 q = 1) : d88252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25254 q ha hb
    | true =>
      simp only [d108828, d88252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25259 q ha hb
  have h7 (q : Pattern) (ha : d10802 q = 1) (hb : d85724 q = 1) : d88254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25248 q ha hb
    | true =>
      simp only [d10802, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10272 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108829 q = 1) : d88255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d88255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108830 q = 1) : d88256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108830, d88256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108831 q = 1) : d88257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108831, d88257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108835 q = 1) : d88261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108835, d88261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25260 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10288 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108836 q = 1) : d88262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108836, d88262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108837 q = 1) : d88263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108837, d88263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108838 q = 1) : d88264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108838, d88264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d108839 q = 1) : d88265 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108839, d88265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d108845 q = 1) : d88280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108845, d88280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25264 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10289 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d108846 q = 1) : d88281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108846, d88281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d108847 q = 1) : d88282 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108847, d88282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d108848 q = 1) : d88283 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108848, d88283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d108849 q = 1) : d88284 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108849, d88284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108850 q = 1) : d88285 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108850, d88285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25266 (p : Pattern) (ha : d85724 p = 1) (hb : d108856 p = 1) : d88291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10270 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108813 q = 1) : d88190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108813, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25245 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108814 q = 1) : d88191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108814, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108815 q = 1) : d88192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108815, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108816 q = 1) : d88193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108816, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108817 q = 1) : d88194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108817, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108851 q = 1) : d88286 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108851, d88286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25265 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108852 q = 1) : d88287 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108852, d88287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108853 q = 1) : d88288 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108853, d88288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108854 q = 1) : d88289 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108854, d88289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108855 q = 1) : d88290 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108855, d88290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108856 q = 1) : d88291 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108856, d88291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25267 (p : Pattern) (ha : d10865 p = 1) (hb : d85723 p = 1) : d88293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10745 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10863 q = 1) (hb : d85721 q = 1) : d10863 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10864 q = 1) (hb : d85723 q = 1) : d88292 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d85723, d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10864, d85723, d88292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10865 q = 1) (hb : d85723 q = 1) : d88293 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10865, d88293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25268 (p : Pattern) (ha : d10875 p = 1) (hb : d85724 p = 1) : d88299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d85724 q = 1) : d88299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25269 (p : Pattern) (ha : d10869 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10863 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10868 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10868, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10869 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25270 (p : Pattern) (ha : d10879 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10877 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10878 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10879 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25271 (p : Pattern) (ha : d10885 p = 1) (hb : d85724 p = 1) : d88305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25268 q ha hb
    | true =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25270 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d85724 q = 1) : d88301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d85724 q = 1) : d88302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d85724 q = 1) : d88303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d85724 q = 1) : d88304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d85724 q = 1) : d88305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d88305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25272 (p : Pattern) (ha : d10888 p = 1) (hb : d85724 p = 1) : d88308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d85724 q = 1) : d88308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25273 (p : Pattern) (ha : d10889 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10877 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10878 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10889 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25274 (p : Pattern) (ha : d10895 p = 1) (hb : d85724 p = 1) : d88314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25268 q ha hb
    | true =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25270 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d85724 q = 1) : d88301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d85724 q = 1) : d88302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d85724 q = 1) : d88303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d85724 q = 1) : d88304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25272 q ha hb
    | true =>
      simp only [d10890, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25273 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d85724 q = 1) : d88310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d88310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d85724 q = 1) : d88311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d88311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d85724 q = 1) : d88312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d88312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d85724 q = 1) : d88313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d88313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d85724 q = 1) : d88314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d88314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25275 (p : Pattern) (ha : d10992 p = 1) (hb : d85724 p = 1) : d140394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25268 q ha hb
    | true =>
      simp only [d10880, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25270 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d85724 q = 1) : d88301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d88301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d85724 q = 1) : d88302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d88302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d85724 q = 1) : d88303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d88303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d85724 q = 1) : d88304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d88304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25270 q ha hb
    | true =>
      simp only [d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d85724 q = 1) : d140394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d140394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d140394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25276 (p : Pattern) (ha : d10998 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25270 q ha hb
    | true =>
      simp only [d10987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25273 q ha hb
    | true =>
      simp only [d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25277 (p : Pattern) (ha : d11007 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25273 q ha hb
    | true =>
      simp only [d10993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25278 (p : Pattern) (ha : d11031 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11030 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11030, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11031 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25279 (p : Pattern) (ha : d11076 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25278 q ha hb
    | true =>
      simp only [d11032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11073 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11074 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11075 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11076 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25280 (p : Pattern) (ha : d11082 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25279 q ha hb
    | true =>
      simp only [d11077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25281 (p : Pattern) (ha : d10900 p = 1) (hb : d85724 p = 1) : d88319 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d85724 q = 1) : d88318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d85724 q = 1) : d88319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d88319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25282 (p : Pattern) (ha : d10902 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10877 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10901 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10902 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25283 (p : Pattern) (ha : d10909 p = 1) (hb : d85724 p = 1) : d88326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d85724 q = 1) : d88324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d85724 q = 1) : d88325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d85724 q = 1) : d88326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d88326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25284 (p : Pattern) (ha : d10912 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10910 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10911 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10912 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25285 (p : Pattern) (ha : d10921 p = 1) (hb : d85723 p = 1) : d88331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10919 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10745 q = 1) (hb : d85721 q = 1) : d10745 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10920 q = 1) (hb : d85723 q = 1) : d88330 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d85723, d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10920, d85723, d88330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10921 q = 1) (hb : d85723 q = 1) : d88331 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10921, d88331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25286 (p : Pattern) (ha : d10927 p = 1) (hb : d85724 p = 1) : d88337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10922 q = 1) (hb : d85723 q = 1) : d88332 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25285 q ha hb
    | true =>
      simp only [d10922, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10923 q = 1) (hb : d85723 q = 1) : d88333 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10923, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10867 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d85724 q = 1) : d88334 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10924, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d85724 q = 1) : d88335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d85724 q = 1) : d88336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d85724 q = 1) : d88337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d88337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25287 (p : Pattern) (ha : d10955 p = 1) (hb : d85724 p = 1) : d88299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10952 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10952, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10953 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10953, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10954 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10954, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10955 q = 1) (hb : d85724 q = 1) : d88299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d88299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25288 (p : Pattern) (ha : d85724 p = 1) (hb : d108861 p = 1) : d140386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d85724 q = 1) : d88320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25281 q ha hb
    | true =>
      simp only [d10903, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25282 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d85724 q = 1) : d88321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d85724 q = 1) : d88322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d85724 q = 1) : d88323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d85724 q = 1) : d88327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25283 q ha hb
    | true =>
      simp only [d10913, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25284 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d85724 q = 1) : d88328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d85724 q = 1) : d88329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d85724 q = 1) : d140381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25286 q ha hb
    | true =>
      simp only [d10928, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25268 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108857 q = 1) : d140382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108857, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25287 q ha hb
    | true =>
      simp only [d10956, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d85724 q = 1) : d88352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108858 q = 1) : d140383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d140383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d140383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108859 q = 1) : d140384 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d140384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108859, d140384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108860 q = 1) : d140385 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d140385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108860, d140385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108861 q = 1) : d140386 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d140386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108861, d140386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25289 (p : Pattern) (ha : d10962 p = 1) (hb : d85724 p = 1) : d88357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d85724 q = 1) : d88318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d88318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d85724 q = 1) : d88357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d88357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25290 (p : Pattern) (ha : d10963 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10877 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10901 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10963 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25291 (p : Pattern) (ha : d10968 p = 1) (hb : d85724 p = 1) : d88362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10871 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10872, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d85724 q = 1) : d88324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d88324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d85724 q = 1) : d88325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d88325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d85724 q = 1) : d88362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d88362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25292 (p : Pattern) (ha : d10969 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10870 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25269 q ha hb
    | true =>
      simp only [d10870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10876 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10876, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10910 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10911 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10969 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25293 (p : Pattern) (ha : d10973 p = 1) (hb : d85724 p = 1) : d88366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d85723 q = 1) : d88332 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25285 q ha hb
    | true =>
      simp only [d10922, d88332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d85723 q = 1) : d88333 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d88333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10867 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10924 q = 1) (hb : d85724 q = 1) : d88334 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d85724, d88334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d85724 q = 1) : d88335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10925, d88335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d85724 q = 1) : d88336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d88336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d85724 q = 1) : d88366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d88366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25294 (p : Pattern) (ha : d10979 p = 1) (hb : d85724 p = 1) : d88308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d85723 q = 1) : d88294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25267 q ha hb
    | true =>
      simp only [d10866, d88294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d85723 q = 1) : d88295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d88295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10952 q = 1) (hb : d85724 q = 1) : d88296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d85724, d88296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10953 q = 1) (hb : d85724 q = 1) : d88297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10953, d88297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10954 q = 1) (hb : d85724 q = 1) : d88298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10954, d88298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10979 q = 1) (hb : d85724 q = 1) : d88308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10979, d88308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25295 (p : Pattern) (ha : d85724 p = 1) (hb : d108866 p = 1) : d140392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d85724 q = 1) : d88320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25281 q ha hb
    | true =>
      simp only [d10903, d88320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25282 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d85724 q = 1) : d88321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d88321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d85724 q = 1) : d88322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d88322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d85724 q = 1) : d88323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d88323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d85724 q = 1) : d88327 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25283 q ha hb
    | true =>
      simp only [d10913, d88327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25284 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d85724 q = 1) : d88328 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d88328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d85724 q = 1) : d88329 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d88329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d85724 q = 1) : d140381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25286 q ha hb
    | true =>
      simp only [d10928, d140381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25268 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108857 q = 1) : d140382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108857, d140382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d85724 q = 1) : d88300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25287 q ha hb
    | true =>
      simp only [d10956, d88300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d85724 q = 1) : d88352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d88352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108858 q = 1) : d140383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d140383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d140383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108859 q = 1) : d140384 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d140384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108859, d140384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108860 q = 1) : d140385 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d140385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108860, d140385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10964 q = 1) (hb : d85724 q = 1) : d88358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25289 q ha hb
    | true =>
      simp only [d10964, d88358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25290 q ha hb
  have h16 (q : Pattern) (ha : d10965 q = 1) (hb : d85724 q = 1) : d88359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d88359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10966 q = 1) (hb : d85724 q = 1) : d88360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10966, d88360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10967 q = 1) (hb : d85724 q = 1) : d88361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d88361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10970 q = 1) (hb : d85724 q = 1) : d88363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25291 q ha hb
    | true =>
      simp only [d10970, d88363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25292 q ha hb
  have h20 (q : Pattern) (ha : d10971 q = 1) (hb : d85724 q = 1) : d88364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d88364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10972 q = 1) (hb : d85724 q = 1) : d88365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10972, d88365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10974 q = 1) (hb : d85724 q = 1) : d140387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25293 q ha hb
    | true =>
      simp only [d10974, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25272 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108862 q = 1) : d140388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108862, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d10980 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25294 q ha hb
    | true =>
      simp only [d10980, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10981 q = 1) (hb : d85724 q = 1) : d88370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10981, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108863 q = 1) : d140389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d140389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108863, d140389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108864 q = 1) : d140390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d140390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108864, d140390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108865 q = 1) : d140391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d140391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108865, d140391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108866 q = 1) : d140392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d140392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108866, d140392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25296 (p : Pattern) (ha : d85724 p = 1) (hb : d108873 p = 1) : d140401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d85724 q = 1) : d140387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25293 q ha hb
    | true =>
      simp only [d10974, d140387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25272 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108862 q = 1) : d140388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108862, d140388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d85724 q = 1) : d88309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25294 q ha hb
    | true =>
      simp only [d10980, d88309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d85724 q = 1) : d88370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d88370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108863 q = 1) : d140389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d140389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d140389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108871 q = 1) : d140399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d140399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108871, d140399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108872 q = 1) : d140400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d140400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108872, d140400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108873 q = 1) : d140401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d140401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108873, d140401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25297 (p : Pattern) (ha : d11018 p = 1) (hb : d85723 p = 1) : d88395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11016 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10817 q = 1) (hb : d85721 q = 1) : d10817 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11017 q = 1) (hb : d85723 q = 1) : d88394 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d85723, d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11017, d85723, d88394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11018 q = 1) (hb : d85723 q = 1) : d88395 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11018, d88395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25298 (p : Pattern) (ha : d11029 p = 1) (hb : d85724 p = 1) : d88401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d85723 q = 1) : d88396 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25297 q ha hb
    | true =>
      simp only [d11019, d88396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d85723 q = 1) : d88397 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d88397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11025 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11026 q = 1) (hb : d85724 q = 1) : d88398 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d85724, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d85724, d88398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d85724 q = 1) : d88399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11027, d88399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d85724 q = 1) : d88400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d88400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d85724 q = 1) : d88401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d88401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25299 (p : Pattern) (ha : d11023 p = 1) (hb : d85723 p = 1) : d88417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11021 q = 1) (hb : d85721 q = 1) : d11021 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11022 q = 1) (hb : d85723 q = 1) : d88416 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d85723, d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11022, d85723, d88416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11023 q = 1) (hb : d85723 q = 1) : d88417 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11023, d88417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25300 (p : Pattern) (ha : d11037 p = 1) (hb : d85724 p = 1) : d88423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d85723 q = 1) : d88418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25299 q ha hb
    | true =>
      simp only [d11024, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d85723 q = 1) : d88419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11033 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11034 q = 1) (hb : d85724 q = 1) : d88420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d85724 q = 1) : d88421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11035, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d85724 q = 1) : d88422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d85724 q = 1) : d88423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25301 (p : Pattern) (ha : d11065 p = 1) (hb : d85724 p = 1) : d88423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d85723 q = 1) : d88418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25299 q ha hb
    | true =>
      simp only [d11024, d88418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d85723 q = 1) : d88419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d88419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11062 q = 1) (hb : d85724 q = 1) : d88420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d85724, d88420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11063 q = 1) (hb : d85724 q = 1) : d88421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11063, d88421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11064 q = 1) (hb : d85724 q = 1) : d88422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11064, d88422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11065 q = 1) (hb : d85724 q = 1) : d88423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11065, d88423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25302 (p : Pattern) (ha : d85724 p = 1) (hb : d108883 p = 1) : d140412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d85724 q = 1) : d140407 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d140407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25298 q ha hb
    | true =>
      simp only [d11038, d140407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25300 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108879 q = 1) : d140408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d140408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108879, d140408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d85724 q = 1) : d88424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25301 q ha hb
    | true =>
      simp only [d11066, d88424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d85724 q = 1) : d88425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d88425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108880 q = 1) : d140409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d140409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d140409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108881 q = 1) : d140410 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d140410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108881, d140410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108882 q = 1) : d140411 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d140411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108882, d140411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108883 q = 1) : d140412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d140412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108883, d140412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25303 (p : Pattern) (ha : d85724 p = 1) (hb : d108889 p = 1) : d140418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d85724 q = 1) : d88306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d88306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25271 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d85724 q = 1) : d88307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d88307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d85724 q = 1) : d88315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25271 q ha hb
    | true =>
      simp only [d10896, d88315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25274 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d85724 q = 1) : d88316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d88316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d85724 q = 1) : d88317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d88317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108867 q = 1) : d140393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d140393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25288 q ha hb
    | true =>
      simp only [d108867, d140393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25295 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d85724 q = 1) : d140395 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d140395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25275 q ha hb
    | true =>
      simp only [d10999, d140395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25276 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108868 q = 1) : d140396 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d140396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d140396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108869 q = 1) : d140397 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d140397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108869, d140397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108870 q = 1) : d140398 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d140398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108870, d140398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108874 q = 1) : d140402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d140402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108874, d140402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25296 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25277 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108875 q = 1) : d140403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d140403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108875, d140403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108876 q = 1) : d140404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d140404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108876, d140404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108877 q = 1) : d140405 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d140405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108877, d140405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d108878 q = 1) : d140406 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d140406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108878, d140406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d108884 q = 1) : d140413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d140413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108884, d140413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25302 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25280 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d108885 q = 1) : d140414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d140414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108885, d140414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d108886 q = 1) : d140415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d140415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108886, d140415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d108887 q = 1) : d140416 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d140416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108887, d140416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d108888 q = 1) : d140417 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d140417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108888, d140417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108889 q = 1) : d140418 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d140418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108889, d140418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25304 (p : Pattern) (ha : d85724 p = 1) (hb : d108895 p = 1) : d140424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d108890 q = 1) : d140419 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d140419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108890, d140419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25303 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108891 q = 1) : d140420 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d140420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108891, d140420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d108892 q = 1) : d140421 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d140421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108892, d140421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d108893 q = 1) : d140422 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d140422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108893, d140422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108894 q = 1) : d140423 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d140423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108894, d140423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108895 q = 1) : d140424 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d140424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108895, d140424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25305 (p : Pattern) (ha : d11105 p = 1) (hb : d85723 p = 1) : d88444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11103 q = 1) (hb : d85721 q = 1) : d11103 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11104 q = 1) (hb : d85723 q = 1) : d88443 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d85723, d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11104, d85723, d88443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11105 q = 1) (hb : d85723 q = 1) : d88444 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11105, d88444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25306 (p : Pattern) (ha : d11115 p = 1) (hb : d85724 p = 1) : d88450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d85724 q = 1) : d88449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d85724 q = 1) : d88450 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d88450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25307 (p : Pattern) (ha : d11109 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11108 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11108, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11109 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25308 (p : Pattern) (ha : d11119 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11119 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25309 (p : Pattern) (ha : d11125 p = 1) (hb : d85724 p = 1) : d88456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25306 q ha hb
    | true =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25308 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d85724 q = 1) : d88452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d85724 q = 1) : d88453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d85724 q = 1) : d88454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d85724 q = 1) : d88455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d85724 q = 1) : d88456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d88456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25310 (p : Pattern) (ha : d11128 p = 1) (hb : d85724 p = 1) : d88459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d85724 q = 1) : d88449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d88449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d85724 q = 1) : d88459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d88459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25311 (p : Pattern) (ha : d11129 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11129 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25312 (p : Pattern) (ha : d11135 p = 1) (hb : d85724 p = 1) : d88465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25306 q ha hb
    | true =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25308 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d85724 q = 1) : d88452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d85724 q = 1) : d88453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d85724 q = 1) : d88454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d85724 q = 1) : d88455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d85724 q = 1) : d88460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25310 q ha hb
    | true =>
      simp only [d11130, d88460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25311 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d85724 q = 1) : d88461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d88461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d85724 q = 1) : d88462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d88462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d85724 q = 1) : d88463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d88463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d85724 q = 1) : d88464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d88464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d85724 q = 1) : d88465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d88465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25313 (p : Pattern) (ha : d11243 p = 1) (hb : d85724 p = 1) : d140452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d85724 q = 1) : d88451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25306 q ha hb
    | true =>
      simp only [d11120, d88451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25308 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d85724 q = 1) : d88452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d88452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d85724 q = 1) : d88453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d88453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d85724 q = 1) : d88454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d88454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d85724 q = 1) : d88455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d88455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25308 q ha hb
    | true =>
      simp only [d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d85724 q = 1) : d140452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d140452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d140452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25314 (p : Pattern) (ha : d11249 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25308 q ha hb
    | true =>
      simp only [d11238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25311 q ha hb
    | true =>
      simp only [d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25315 (p : Pattern) (ha : d11258 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25311 q ha hb
    | true =>
      simp only [d11244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25316 (p : Pattern) (ha : d11289 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11279 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11288 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11288, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11289 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25317 (p : Pattern) (ha : d11345 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25316 q ha hb
    | true =>
      simp only [d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11342 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11343 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11344 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11345 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25318 (p : Pattern) (ha : d11351 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25317 q ha hb
    | true =>
      simp only [d11346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25319 (p : Pattern) (ha : d11140 p = 1) (hb : d85724 p = 1) : d88470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d85724 q = 1) : d88469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d85724 q = 1) : d88470 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d88470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25320 (p : Pattern) (ha : d11142 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11141 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11142 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25321 (p : Pattern) (ha : d11149 p = 1) (hb : d85724 p = 1) : d88477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d85724 q = 1) : d88475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d85724 q = 1) : d88476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d85724 q = 1) : d88477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d88477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25322 (p : Pattern) (ha : d11152 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11150 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11151 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11152 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25323 (p : Pattern) (ha : d11161 p = 1) (hb : d85723 p = 1) : d88482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11159 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11102 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11160 q = 1) (hb : d85723 q = 1) : d88481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d85723, d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11160, d85723, d88481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11161 q = 1) (hb : d85723 q = 1) : d88482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11161, d88482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25324 (p : Pattern) (ha : d11167 p = 1) (hb : d85724 p = 1) : d88488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11162 q = 1) (hb : d85723 q = 1) : d88483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25323 q ha hb
    | true =>
      simp only [d11162, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11163 q = 1) (hb : d85723 q = 1) : d88484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11163, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d85724 q = 1) : d88485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11164, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d85724 q = 1) : d88486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d85724 q = 1) : d88487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d85724 q = 1) : d88488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d88488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25325 (p : Pattern) (ha : d11200 p = 1) (hb : d85723 p = 1) : d140429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11102 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11198 q = 1) (hb : d85721 q = 1) : d11198 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11199 q = 1) (hb : d85723 q = 1) : d140428 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d85723, d140428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11199, d85723, d140428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11200 q = 1) (hb : d85723 q = 1) : d140429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d140429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11200, d140429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25326 (p : Pattern) (ha : d11206 p = 1) (hb : d85724 p = 1) : d140435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11201 q = 1) (hb : d85723 q = 1) : d140430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d140430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25325 q ha hb
    | true =>
      simp only [d11201, d140430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11202 q = 1) (hb : d85723 q = 1) : d140431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d140431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11202, d140431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11203 q = 1) (hb : d85724 q = 1) : d140432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d85724, d140432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11203, d85724, d140432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11204 q = 1) (hb : d85724 q = 1) : d140433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d140433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11204, d140433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11205 q = 1) (hb : d85724 q = 1) : d140434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d140434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11205, d140434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11206 q = 1) (hb : d85724 q = 1) : d140435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d140435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d140435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25327 (p : Pattern) (ha : d85724 p = 1) (hb : d108901 p = 1) : d140441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d85724 q = 1) : d88471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25319 q ha hb
    | true =>
      simp only [d11143, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25320 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d85724 q = 1) : d88472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d85724 q = 1) : d88473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d85724 q = 1) : d88474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d85724 q = 1) : d88478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25321 q ha hb
    | true =>
      simp only [d11153, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25322 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d85724 q = 1) : d88479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d85724 q = 1) : d88480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d85724 q = 1) : d140426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25324 q ha hb
    | true =>
      simp only [d11168, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25306 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108897 q = 1) : d140427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108897, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d85724 q = 1) : d140436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d140436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25326 q ha hb
    | true =>
      simp only [d11207, d140436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d85724 q = 1) : d140437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d140437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d140437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108898 q = 1) : d140438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d140438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d140438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108899 q = 1) : d140439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d140439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108899, d140439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108900 q = 1) : d140440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d140440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108900, d140440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108901 q = 1) : d140441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d140441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108901, d140441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25328 (p : Pattern) (ha : d11213 p = 1) (hb : d85724 p = 1) : d88508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d85724 q = 1) : d88448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d88448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d85724 q = 1) : d88469 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d88469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d85724 q = 1) : d88508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d88508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25329 (p : Pattern) (ha : d11214 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11141 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11214 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25330 (p : Pattern) (ha : d11219 p = 1) (hb : d85724 p = 1) : d88513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11106 q = 1) (hb : d85723 q = 1) : d88445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25305 q ha hb
    | true =>
      simp only [d11106, d88445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11107 q = 1) (hb : d85723 q = 1) : d88446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11107, d88446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11111 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d85724 q = 1) : d88447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11112, d85724, d88447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d85724 q = 1) : d88475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d88475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d85724 q = 1) : d88476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d88476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d85724 q = 1) : d88513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d88513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25331 (p : Pattern) (ha : d11220 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11110 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25307 q ha hb
    | true =>
      simp only [d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11116 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11116, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11150 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11151 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11220 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25332 (p : Pattern) (ha : d11224 p = 1) (hb : d85724 p = 1) : d88517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d85723 q = 1) : d88483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25323 q ha hb
    | true =>
      simp only [d11162, d88483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d85723 q = 1) : d88484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d88484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11164 q = 1) (hb : d85724 q = 1) : d88485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d85724, d88485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d85724 q = 1) : d88486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11165, d88486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d85724 q = 1) : d88487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d88487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d85724 q = 1) : d88517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d88517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25333 (p : Pattern) (ha : d11230 p = 1) (hb : d85724 p = 1) : d140444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d85723 q = 1) : d140430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d140430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25325 q ha hb
    | true =>
      simp only [d11201, d140430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d85723 q = 1) : d140431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d140431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d140431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11203 q = 1) (hb : d85724 q = 1) : d140432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d85724, d140432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d85724, d140432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11204 q = 1) (hb : d85724 q = 1) : d140433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d140433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11204, d140433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11205 q = 1) (hb : d85724 q = 1) : d140434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d140434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11205, d140434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11230 q = 1) (hb : d85724 q = 1) : d140444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d140444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11230, d140444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25334 (p : Pattern) (ha : d85724 p = 1) (hb : d108906 p = 1) : d140450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d85724 q = 1) : d88471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25319 q ha hb
    | true =>
      simp only [d11143, d88471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25320 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d85724 q = 1) : d88472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d88472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d85724 q = 1) : d88473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d88473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d85724 q = 1) : d88474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d88474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d85724 q = 1) : d88478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25321 q ha hb
    | true =>
      simp only [d11153, d88478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25322 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d85724 q = 1) : d88479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d88479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d85724 q = 1) : d88480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d88480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d85724 q = 1) : d140426 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25324 q ha hb
    | true =>
      simp only [d11168, d140426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25306 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108897 q = 1) : d140427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108897, d140427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d85724 q = 1) : d140436 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d140436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25326 q ha hb
    | true =>
      simp only [d11207, d140436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d85724 q = 1) : d140437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d140437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d140437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108898 q = 1) : d140438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d140438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d140438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108899 q = 1) : d140439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d140439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108899, d140439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108900 q = 1) : d140440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d140440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108900, d140440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11215 q = 1) (hb : d85724 q = 1) : d88509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25328 q ha hb
    | true =>
      simp only [d11215, d88509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25329 q ha hb
  have h16 (q : Pattern) (ha : d11216 q = 1) (hb : d85724 q = 1) : d88510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d88510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11217 q = 1) (hb : d85724 q = 1) : d88511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11217, d88511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11218 q = 1) (hb : d85724 q = 1) : d88512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d88512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11221 q = 1) (hb : d85724 q = 1) : d88514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25330 q ha hb
    | true =>
      simp only [d11221, d88514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25331 q ha hb
  have h20 (q : Pattern) (ha : d11222 q = 1) (hb : d85724 q = 1) : d88515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d88515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11223 q = 1) (hb : d85724 q = 1) : d88516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11223, d88516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11225 q = 1) (hb : d85724 q = 1) : d140442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25332 q ha hb
    | true =>
      simp only [d11225, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25310 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108902 q = 1) : d140443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108902, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d11231 q = 1) (hb : d85724 q = 1) : d140445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d140445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25333 q ha hb
    | true =>
      simp only [d11231, d140445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11232 q = 1) (hb : d85724 q = 1) : d140446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d140446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11232, d140446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108903 q = 1) : d140447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d140447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108903, d140447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108904 q = 1) : d140448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d140448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108904, d140448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108905 q = 1) : d140449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d140449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108905, d140449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108906 q = 1) : d140450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d140450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108906, d140450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25335 (p : Pattern) (ha : d85724 p = 1) (hb : d108913 p = 1) : d140459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d85724 q = 1) : d140442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25332 q ha hb
    | true =>
      simp only [d11225, d140442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25310 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108902 q = 1) : d140443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108902, d140443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d85724 q = 1) : d140445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d140445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25333 q ha hb
    | true =>
      simp only [d11231, d140445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d85724 q = 1) : d140446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d140446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d140446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108903 q = 1) : d140447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d140447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d140447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108911 q = 1) : d140457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d140457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108911, d140457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108912 q = 1) : d140458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d140458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108912, d140458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108913 q = 1) : d140459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d140459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108913, d140459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25336 (p : Pattern) (ha : d11276 p = 1) (hb : d85723 p = 1) : d88546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11270 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11274 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11275 q = 1) (hb : d85723 q = 1) : d88545 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d85723, d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11275, d85723, d88545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11276 q = 1) (hb : d85723 q = 1) : d88546 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11276, d88546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25337 (p : Pattern) (ha : d11287 p = 1) (hb : d85724 p = 1) : d88552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d85723 q = 1) : d88547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25336 q ha hb
    | true =>
      simp only [d11277, d88547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d85723 q = 1) : d88548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d88548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11283 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11284 q = 1) (hb : d85724 q = 1) : d88549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d85724, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d85724, d88549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d85724 q = 1) : d88550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11285, d88550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d85724 q = 1) : d88551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d88551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d85724 q = 1) : d88552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d88552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25338 (p : Pattern) (ha : d11281 p = 1) (hb : d85723 p = 1) : d88568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11274 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11279 q = 1) (hb : d85721 q = 1) : d11279 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11280 q = 1) (hb : d85723 q = 1) : d88567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d85723, d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11280, d85723, d88567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11281 q = 1) (hb : d85723 q = 1) : d88568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11281, d88568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25339 (p : Pattern) (ha : d11295 p = 1) (hb : d85724 p = 1) : d88574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d85723 q = 1) : d88569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25338 q ha hb
    | true =>
      simp only [d11282, d88569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d85723 q = 1) : d88570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d88570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11292 q = 1) (hb : d85724 q = 1) : d88571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d85724, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d85724, d88571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11293 q = 1) (hb : d85724 q = 1) : d88572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11293, d88572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11294 q = 1) (hb : d85724 q = 1) : d88573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11294, d88573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11295 q = 1) (hb : d85724 q = 1) : d88574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11295, d88574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25340 (p : Pattern) (ha : d11328 p = 1) (hb : d85723 p = 1) : d140468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11274 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11326 q = 1) (hb : d85721 q = 1) : d11326 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11327 q = 1) (hb : d85723 q = 1) : d140467 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d85723, d140467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11327, d85723, d140467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11328 q = 1) (hb : d85723 q = 1) : d140468 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d140468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11328, d140468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25341 (p : Pattern) (ha : d11334 p = 1) (hb : d85724 p = 1) : d140474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d85723 q = 1) : d140469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d140469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25340 q ha hb
    | true =>
      simp only [d11329, d140469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d85723 q = 1) : d140470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d140470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d140470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11331 q = 1) (hb : d85724 q = 1) : d140471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d85724, d140471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d85724, d140471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11332 q = 1) (hb : d85724 q = 1) : d140472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d140472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11332, d140472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11333 q = 1) (hb : d85724 q = 1) : d140473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d140473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11333, d140473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11334 q = 1) (hb : d85724 q = 1) : d140474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d140474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11334, d140474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25342 (p : Pattern) (ha : d85724 p = 1) (hb : d108923 p = 1) : d140480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d85724 q = 1) : d140465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d140465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25337 q ha hb
    | true =>
      simp only [d11296, d140465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25339 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108919 q = 1) : d140466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d140466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108919, d140466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d85724 q = 1) : d140475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d140475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25341 q ha hb
    | true =>
      simp only [d11335, d140475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d85724 q = 1) : d140476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d140476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d140476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108920 q = 1) : d140477 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d140477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d140477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108921 q = 1) : d140478 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d140478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108921, d140478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108922 q = 1) : d140479 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d140479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108922, d140479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108923 q = 1) : d140480 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d140480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108923, d140480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25343 (p : Pattern) (ha : d85724 p = 1) (hb : d108929 p = 1) : d140486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d85724 q = 1) : d88457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d88457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25309 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d85724 q = 1) : d88458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d88458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d85724 q = 1) : d88466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25309 q ha hb
    | true =>
      simp only [d11136, d88466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25312 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d85724 q = 1) : d88467 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d88467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d85724 q = 1) : d88468 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d88468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108907 q = 1) : d140451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d140451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25327 q ha hb
    | true =>
      simp only [d108907, d140451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25334 q ha hb
  have h7 (q : Pattern) (ha : d11250 q = 1) (hb : d85724 q = 1) : d140453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d140453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25313 q ha hb
    | true =>
      simp only [d11250, d140453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25314 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108908 q = 1) : d140454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d140454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d140454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108909 q = 1) : d140455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d140455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108909, d140455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108910 q = 1) : d140456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d140456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108910, d140456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108914 q = 1) : d140460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d140460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108914, d140460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25335 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25315 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108915 q = 1) : d140461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d140461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108915, d140461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108916 q = 1) : d140462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d140462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108916, d140462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108917 q = 1) : d140463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d140463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108917, d140463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d108918 q = 1) : d140464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d140464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108918, d140464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d108924 q = 1) : d140481 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d140481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108924, d140481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25342 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25318 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d108925 q = 1) : d140482 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d140482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108925, d140482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d108926 q = 1) : d140483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d140483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108926, d140483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d108927 q = 1) : d140484 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d140484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108927, d140484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d108928 q = 1) : d140485 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d140485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108928, d140485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108929 q = 1) : d140486 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d140486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108929, d140486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25344 (p : Pattern) (ha : d85724 p = 1) (hb : d108935 p = 1) : d140492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d108930 q = 1) : d140487 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d140487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108930, d140487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25343 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108931 q = 1) : d140488 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d140488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108931, d140488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d108932 q = 1) : d140489 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d140489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108932, d140489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d108933 q = 1) : d140490 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d140490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108933, d140490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108934 q = 1) : d140491 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d140491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108934, d140491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108935 q = 1) : d140492 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d140492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108935, d140492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25345 (p : Pattern) (ha : d11375 p = 1) (hb : d85723 p = 1) : d88596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11372 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11373 q = 1) (hb : d85721 q = 1) : d11373 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11374 q = 1) (hb : d85723 q = 1) : d88595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d85723, d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11374, d85723, d88595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11375 q = 1) (hb : d85723 q = 1) : d88596 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11375, d88596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25346 (p : Pattern) (ha : d11385 p = 1) (hb : d85724 p = 1) : d88602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d85724 q = 1) : d88601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11385 q = 1) (hb : d85724 q = 1) : d88602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d88602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25347 (p : Pattern) (ha : d11379 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11373 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11378 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11378, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11379 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25348 (p : Pattern) (ha : d11389 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11387 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11388 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11389 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25349 (p : Pattern) (ha : d11395 p = 1) (hb : d85724 p = 1) : d88608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25346 q ha hb
    | true =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25348 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d85724 q = 1) : d88604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d85724 q = 1) : d88605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d85724 q = 1) : d88606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d85724 q = 1) : d88607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11395 q = 1) (hb : d85724 q = 1) : d88608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d88608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25350 (p : Pattern) (ha : d11398 p = 1) (hb : d85724 p = 1) : d88611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d85724 q = 1) : d88601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d88601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11398 q = 1) (hb : d85724 q = 1) : d88611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11398, d88611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25351 (p : Pattern) (ha : d11399 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11387 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11388 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11399 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25352 (p : Pattern) (ha : d11405 p = 1) (hb : d85724 p = 1) : d88617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25346 q ha hb
    | true =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25348 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d85724 q = 1) : d88604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d85724 q = 1) : d88605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d85724 q = 1) : d88606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d85724 q = 1) : d88607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11400 q = 1) (hb : d85724 q = 1) : d88612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25350 q ha hb
    | true =>
      simp only [d11400, d88612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25351 q ha hb
  have h7 (q : Pattern) (ha : d11401 q = 1) (hb : d85724 q = 1) : d88613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d88613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11402 q = 1) (hb : d85724 q = 1) : d88614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11402, d88614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11403 q = 1) (hb : d85724 q = 1) : d88615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d88615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11404 q = 1) (hb : d85724 q = 1) : d88616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d88616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11405 q = 1) (hb : d85724 q = 1) : d88617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11405, d88617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25353 (p : Pattern) (ha : d11513 p = 1) (hb : d85724 p = 1) : d140521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d85724 q = 1) : d88603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25346 q ha hb
    | true =>
      simp only [d11390, d88603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25348 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d85724 q = 1) : d88604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d88604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d85724 q = 1) : d88605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d88605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d85724 q = 1) : d88606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d88606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d85724 q = 1) : d88607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d88607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25348 q ha hb
    | true =>
      simp only [d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11513 q = 1) (hb : d85724 q = 1) : d140521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d140521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11513, d140521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25354 (p : Pattern) (ha : d11519 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11508 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25348 q ha hb
    | true =>
      simp only [d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11509 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11510 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11511 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11512 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11514 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25351 q ha hb
    | true =>
      simp only [d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11515 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11516 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11517 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11518 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11519 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25355 (p : Pattern) (ha : d11528 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11514 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25351 q ha hb
    | true =>
      simp only [d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11515 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11516 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11517 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11518 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11528 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25356 (p : Pattern) (ha : d11559 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11549 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11558 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11558, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11559 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25357 (p : Pattern) (ha : d11615 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11560 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25356 q ha hb
    | true =>
      simp only [d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11561 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11612 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11612, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11613 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11614 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11615 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25358 (p : Pattern) (ha : d11621 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11616 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25357 q ha hb
    | true =>
      simp only [d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11617 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11618 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11619 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11620 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11621 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25359 (p : Pattern) (ha : d11410 p = 1) (hb : d85724 p = 1) : d88622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d85724 q = 1) : d88621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11410 q = 1) (hb : d85724 q = 1) : d88622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d88622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25360 (p : Pattern) (ha : d11412 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11387 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11411 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11412 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25361 (p : Pattern) (ha : d11419 p = 1) (hb : d85724 p = 1) : d88629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d85724 q = 1) : d88627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d85724 q = 1) : d88628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11419 q = 1) (hb : d85724 q = 1) : d88629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d88629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25362 (p : Pattern) (ha : d11422 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11420 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11421 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11422 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25363 (p : Pattern) (ha : d11431 p = 1) (hb : d85723 p = 1) : d88634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11429 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11372 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11430 q = 1) (hb : d85723 q = 1) : d88633 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d85723, d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11430, d85723, d88633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11431 q = 1) (hb : d85723 q = 1) : d88634 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11431, d88634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25364 (p : Pattern) (ha : d11437 p = 1) (hb : d85724 p = 1) : d88640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11432 q = 1) (hb : d85723 q = 1) : d88635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25363 q ha hb
    | true =>
      simp only [d11432, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11433 q = 1) (hb : d85723 q = 1) : d88636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11433, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11377 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d85724 q = 1) : d88637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11434, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d85724 q = 1) : d88638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d85724 q = 1) : d88639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d85724 q = 1) : d88640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d88640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25365 (p : Pattern) (ha : d11470 p = 1) (hb : d85723 p = 1) : d140498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11372 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11468 q = 1) (hb : d85721 q = 1) : d11468 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11469 q = 1) (hb : d85723 q = 1) : d140497 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d85723, d140497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11469, d85723, d140497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11470 q = 1) (hb : d85723 q = 1) : d140498 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d140498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11470, d140498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25366 (p : Pattern) (ha : d11476 p = 1) (hb : d85724 p = 1) : d140504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11471 q = 1) (hb : d85723 q = 1) : d140499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d140499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25365 q ha hb
    | true =>
      simp only [d11471, d140499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11472 q = 1) (hb : d85723 q = 1) : d140500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d140500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11472, d140500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11473 q = 1) (hb : d85724 q = 1) : d140501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d85724, d140501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11473, d85724, d140501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11474 q = 1) (hb : d85724 q = 1) : d140502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d140502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11474, d140502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11475 q = 1) (hb : d85724 q = 1) : d140503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d140503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11475, d140503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11476 q = 1) (hb : d85724 q = 1) : d140504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d140504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d140504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25367 (p : Pattern) (ha : d85724 p = 1) (hb : d108942 p = 1) : d140510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d85724 q = 1) : d88623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25359 q ha hb
    | true =>
      simp only [d11413, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25360 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d85724 q = 1) : d88624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d85724 q = 1) : d88625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d85724 q = 1) : d88626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d85724 q = 1) : d88630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25361 q ha hb
    | true =>
      simp only [d11423, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25362 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d85724 q = 1) : d88631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d85724 q = 1) : d88632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d85724 q = 1) : d140495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25364 q ha hb
    | true =>
      simp only [d11438, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25346 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108938 q = 1) : d140496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108938, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d85724 q = 1) : d140505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d140505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25366 q ha hb
    | true =>
      simp only [d11477, d140505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d85724 q = 1) : d140506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d140506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d140506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108939 q = 1) : d140507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d140507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d140507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108940 q = 1) : d140508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d140508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108940, d140508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108941 q = 1) : d140509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d140509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108941, d140509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108942 q = 1) : d140510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d140510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108942, d140510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25368 (p : Pattern) (ha : d11483 p = 1) (hb : d85724 p = 1) : d88660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d85724 q = 1) : d88600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d88600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d85724 q = 1) : d88621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d88621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11483 q = 1) (hb : d85724 q = 1) : d88660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11483, d88660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25369 (p : Pattern) (ha : d11484 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11387 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11411 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11484 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25370 (p : Pattern) (ha : d11489 p = 1) (hb : d85724 p = 1) : d88665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11376 q = 1) (hb : d85723 q = 1) : d88597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25345 q ha hb
    | true =>
      simp only [d11376, d88597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11377 q = 1) (hb : d85723 q = 1) : d88598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11377, d88598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d85724 q = 1) : d88599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11382, d85724, d88599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d85724 q = 1) : d88627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d88627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d85724 q = 1) : d88628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d88628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11489 q = 1) (hb : d85724 q = 1) : d88665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11489, d88665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25371 (p : Pattern) (ha : d11490 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11380 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25347 q ha hb
    | true =>
      simp only [d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11386 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11386, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11420 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11421 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11490 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25372 (p : Pattern) (ha : d11494 p = 1) (hb : d85724 p = 1) : d88669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d85723 q = 1) : d88635 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25363 q ha hb
    | true =>
      simp only [d11432, d88635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d85723 q = 1) : d88636 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d88636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11434 q = 1) (hb : d85724 q = 1) : d88637 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d85724, d88637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d85724 q = 1) : d88638 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11435, d88638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d85724 q = 1) : d88639 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d88639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d85724 q = 1) : d88669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d88669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25373 (p : Pattern) (ha : d11500 p = 1) (hb : d85724 p = 1) : d140513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d85723 q = 1) : d140499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d140499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25365 q ha hb
    | true =>
      simp only [d11471, d140499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d85723 q = 1) : d140500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d140500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d140500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11473 q = 1) (hb : d85724 q = 1) : d140501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d85724, d140501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d85724, d140501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11474 q = 1) (hb : d85724 q = 1) : d140502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d140502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11474, d140502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11475 q = 1) (hb : d85724 q = 1) : d140503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d140503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11475, d140503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11500 q = 1) (hb : d85724 q = 1) : d140513 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d140513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11500, d140513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25374 (p : Pattern) (ha : d85724 p = 1) (hb : d108947 p = 1) : d140519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d85724 q = 1) : d88623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25359 q ha hb
    | true =>
      simp only [d11413, d88623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25360 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d85724 q = 1) : d88624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d88624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d85724 q = 1) : d88625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d88625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d85724 q = 1) : d88626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d88626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d85724 q = 1) : d88630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25361 q ha hb
    | true =>
      simp only [d11423, d88630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25362 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d85724 q = 1) : d88631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d88631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d85724 q = 1) : d88632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d88632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d85724 q = 1) : d140495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25364 q ha hb
    | true =>
      simp only [d11438, d140495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25346 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108938 q = 1) : d140496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108938, d140496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d85724 q = 1) : d140505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d140505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25366 q ha hb
    | true =>
      simp only [d11477, d140505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d85724 q = 1) : d140506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d140506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d140506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108939 q = 1) : d140507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d140507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d140507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108940 q = 1) : d140508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d140508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108940, d140508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108941 q = 1) : d140509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d140509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108941, d140509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11485 q = 1) (hb : d85724 q = 1) : d88661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25368 q ha hb
    | true =>
      simp only [d11485, d88661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25369 q ha hb
  have h16 (q : Pattern) (ha : d11486 q = 1) (hb : d85724 q = 1) : d88662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d88662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11487 q = 1) (hb : d85724 q = 1) : d88663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11487, d88663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11488 q = 1) (hb : d85724 q = 1) : d88664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d88664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11491 q = 1) (hb : d85724 q = 1) : d88666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25370 q ha hb
    | true =>
      simp only [d11491, d88666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25371 q ha hb
  have h20 (q : Pattern) (ha : d11492 q = 1) (hb : d85724 q = 1) : d88667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d88667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11493 q = 1) (hb : d85724 q = 1) : d88668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11493, d88668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11495 q = 1) (hb : d85724 q = 1) : d140511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25372 q ha hb
    | true =>
      simp only [d11495, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25350 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108943 q = 1) : d140512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108943, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d11501 q = 1) (hb : d85724 q = 1) : d140514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d140514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25373 q ha hb
    | true =>
      simp only [d11501, d140514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11502 q = 1) (hb : d85724 q = 1) : d140515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d140515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11502, d140515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108944 q = 1) : d140516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d140516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108944, d140516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108945 q = 1) : d140517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d140517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108945, d140517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108946 q = 1) : d140518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d140518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108946, d140518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108947 q = 1) : d140519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d140519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108947, d140519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25375 (p : Pattern) (ha : d85724 p = 1) (hb : d108954 p = 1) : d140528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d85724 q = 1) : d140511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25372 q ha hb
    | true =>
      simp only [d11495, d140511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25350 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108943 q = 1) : d140512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108943, d140512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d85724 q = 1) : d140514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d140514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25373 q ha hb
    | true =>
      simp only [d11501, d140514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d85724 q = 1) : d140515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d140515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d140515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108944 q = 1) : d140516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d140516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d140516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108952 q = 1) : d140526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d140526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108952, d140526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108953 q = 1) : d140527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d140527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108953, d140527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108954 q = 1) : d140528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d140528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108954, d140528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25376 (p : Pattern) (ha : d11546 p = 1) (hb : d85723 p = 1) : d88698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11540 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11544 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11545 q = 1) (hb : d85723 q = 1) : d88697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d85723, d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11545, d85723, d88697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11546 q = 1) (hb : d85723 q = 1) : d88698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11546, d88698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25377 (p : Pattern) (ha : d11557 p = 1) (hb : d85724 p = 1) : d88704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d85723 q = 1) : d88699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25376 q ha hb
    | true =>
      simp only [d11547, d88699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d85723 q = 1) : d88700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d88700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11553 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11554 q = 1) (hb : d85724 q = 1) : d88701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d85724, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d85724, d88701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d85724 q = 1) : d88702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11555, d88702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d85724 q = 1) : d88703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d88703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d85724 q = 1) : d88704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d88704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25378 (p : Pattern) (ha : d11551 p = 1) (hb : d85723 p = 1) : d88720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11549 q = 1) (hb : d85721 q = 1) : d11549 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11550 q = 1) (hb : d85723 q = 1) : d88719 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d85723, d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11550, d85723, d88719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11551 q = 1) (hb : d85723 q = 1) : d88720 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11551, d88720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25379 (p : Pattern) (ha : d11565 p = 1) (hb : d85724 p = 1) : d88726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d85723 q = 1) : d88721 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25378 q ha hb
    | true =>
      simp only [d11552, d88721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d85723 q = 1) : d88722 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d88722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11561 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11562 q = 1) (hb : d85724 q = 1) : d88723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d85724, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d85724, d88723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11563 q = 1) (hb : d85724 q = 1) : d88724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11563, d88724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11564 q = 1) (hb : d85724 q = 1) : d88725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11564, d88725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11565 q = 1) (hb : d85724 q = 1) : d88726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11565, d88726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25380 (p : Pattern) (ha : d11598 p = 1) (hb : d85723 p = 1) : d140537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11596 q = 1) (hb : d85721 q = 1) : d11596 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11597 q = 1) (hb : d85723 q = 1) : d140536 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d85723, d140536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11597, d85723, d140536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11598 q = 1) (hb : d85723 q = 1) : d140537 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d140537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11598, d140537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25381 (p : Pattern) (ha : d11604 p = 1) (hb : d85724 p = 1) : d140543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d85723 q = 1) : d140538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d140538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25380 q ha hb
    | true =>
      simp only [d11599, d140538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d85723 q = 1) : d140539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d140539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d140539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11601 q = 1) (hb : d85724 q = 1) : d140540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d85724, d140540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d85724, d140540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11602 q = 1) (hb : d85724 q = 1) : d140541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d140541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11602, d140541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11603 q = 1) (hb : d85724 q = 1) : d140542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d140542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11603, d140542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11604 q = 1) (hb : d85724 q = 1) : d140543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d140543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11604, d140543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25382 (p : Pattern) (ha : d85724 p = 1) (hb : d108964 p = 1) : d140549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d85724 q = 1) : d140534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d140534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25377 q ha hb
    | true =>
      simp only [d11566, d140534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25379 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108960 q = 1) : d140535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d140535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108960, d140535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d85724 q = 1) : d140544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d140544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25381 q ha hb
    | true =>
      simp only [d11605, d140544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d85724 q = 1) : d140545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d140545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d140545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108961 q = 1) : d140546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d140546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d140546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108962 q = 1) : d140547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d140547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108962, d140547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108963 q = 1) : d140548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d140548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108963, d140548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108964 q = 1) : d140549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d140549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108964, d140549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25383 (p : Pattern) (ha : d85724 p = 1) (hb : d108970 p = 1) : d140555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d85724 q = 1) : d88609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d88609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25349 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d85724 q = 1) : d88610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d88610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d85724 q = 1) : d88618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25349 q ha hb
    | true =>
      simp only [d11406, d88618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25352 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d85724 q = 1) : d88619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d88619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d85724 q = 1) : d88620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d88620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108948 q = 1) : d140520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d140520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25367 q ha hb
    | true =>
      simp only [d108948, d140520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25374 q ha hb
  have h7 (q : Pattern) (ha : d11520 q = 1) (hb : d85724 q = 1) : d140522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d140522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25353 q ha hb
    | true =>
      simp only [d11520, d140522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25354 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108949 q = 1) : d140523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d140523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d140523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108950 q = 1) : d140524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d140524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108950, d140524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108951 q = 1) : d140525 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d140525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108951, d140525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108955 q = 1) : d140529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d140529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108955, d140529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25375 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25355 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108956 q = 1) : d140530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d140530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108956, d140530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108957 q = 1) : d140531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d140531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108957, d140531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108958 q = 1) : d140532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d140532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108958, d140532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d108959 q = 1) : d140533 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d140533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108959, d140533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d108965 q = 1) : d140550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d140550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108965, d140550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25382 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25358 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d108966 q = 1) : d140551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d140551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108966, d140551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d108967 q = 1) : d140552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d140552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108967, d140552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d108968 q = 1) : d140553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d140553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108968, d140553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d108969 q = 1) : d140554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d140554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108969, d140554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108970 q = 1) : d140555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d140555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108970, d140555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25384 (p : Pattern) (ha : d85724 p = 1) (hb : d108976 p = 1) : d140561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d108971 q = 1) : d140556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d140556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108971, d140556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25383 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108972 q = 1) : d140557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d140557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108972, d140557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d108973 q = 1) : d140558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d140558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108973, d140558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d108974 q = 1) : d140559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d140559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108974, d140559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108975 q = 1) : d140560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d140560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108975, d140560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108976 q = 1) : d140561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d140561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108976, d140561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25385 (p : Pattern) (ha : d11646 p = 1) (hb : d85723 p = 1) : d88749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11644 q = 1) (hb : d85721 q = 1) : d11644 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11645 q = 1) (hb : d85723 q = 1) : d88748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d85723, d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11645, d85723, d88748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11646 q = 1) (hb : d85723 q = 1) : d88749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11646, d88749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25386 (p : Pattern) (ha : d11656 p = 1) (hb : d85724 p = 1) : d88755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d85724 q = 1) : d88754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11656 q = 1) (hb : d85724 q = 1) : d88755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d88755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25387 (p : Pattern) (ha : d11650 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11644 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11649 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11649, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11650 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25388 (p : Pattern) (ha : d11660 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11658 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11659 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11660 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25389 (p : Pattern) (ha : d11666 p = 1) (hb : d85724 p = 1) : d88761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25386 q ha hb
    | true =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25388 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d85724 q = 1) : d88757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d85724 q = 1) : d88758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d85724 q = 1) : d88759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d85724 q = 1) : d88760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11666 q = 1) (hb : d85724 q = 1) : d88761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d88761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25390 (p : Pattern) (ha : d11669 p = 1) (hb : d85724 p = 1) : d88764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d85724 q = 1) : d88754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d88754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11669 q = 1) (hb : d85724 q = 1) : d88764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11669, d88764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25391 (p : Pattern) (ha : d11670 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11658 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11659 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11670 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25392 (p : Pattern) (ha : d11676 p = 1) (hb : d85724 p = 1) : d88770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25386 q ha hb
    | true =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25388 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d85724 q = 1) : d88757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d85724 q = 1) : d88758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d85724 q = 1) : d88759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d85724 q = 1) : d88760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11671 q = 1) (hb : d85724 q = 1) : d88765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25390 q ha hb
    | true =>
      simp only [d11671, d88765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25391 q ha hb
  have h7 (q : Pattern) (ha : d11672 q = 1) (hb : d85724 q = 1) : d88766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d88766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11673 q = 1) (hb : d85724 q = 1) : d88767 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11673, d88767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11674 q = 1) (hb : d85724 q = 1) : d88768 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d88768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11675 q = 1) (hb : d85724 q = 1) : d88769 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d88769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11676 q = 1) (hb : d85724 q = 1) : d88770 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11676, d88770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25393 (p : Pattern) (ha : d11784 p = 1) (hb : d85724 p = 1) : d140591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d85724 q = 1) : d88756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25386 q ha hb
    | true =>
      simp only [d11661, d88756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25388 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d85724 q = 1) : d88757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d88757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d85724 q = 1) : d88758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d88758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d85724 q = 1) : d88759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d88759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d85724 q = 1) : d88760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d88760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25388 q ha hb
    | true =>
      simp only [d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11784 q = 1) (hb : d85724 q = 1) : d140591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d140591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11784, d140591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25394 (p : Pattern) (ha : d11790 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11779 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25388 q ha hb
    | true =>
      simp only [d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11780 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11781 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11782 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11783 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11785 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25391 q ha hb
    | true =>
      simp only [d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11786 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11787 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11788 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11789 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11790 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25395 (p : Pattern) (ha : d11799 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11785 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25391 q ha hb
    | true =>
      simp only [d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11786 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11787 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11788 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11789 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11799 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25396 (p : Pattern) (ha : d11830 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11820 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11829 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11829, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11830 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25397 (p : Pattern) (ha : d11886 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11831 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25396 q ha hb
    | true =>
      simp only [d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11832 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11883 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11883, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11884 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11885 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11886 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25398 (p : Pattern) (ha : d11892 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11887 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25397 q ha hb
    | true =>
      simp only [d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11888 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11889 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11890 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11891 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11892 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25399 (p : Pattern) (ha : d11681 p = 1) (hb : d85724 p = 1) : d88775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d85724 q = 1) : d88774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11681 q = 1) (hb : d85724 q = 1) : d88775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d88775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25400 (p : Pattern) (ha : d11683 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11658 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11682 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11683 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25401 (p : Pattern) (ha : d11690 p = 1) (hb : d85724 p = 1) : d88782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d85724 q = 1) : d88780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d85724 q = 1) : d88781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11690 q = 1) (hb : d85724 q = 1) : d88782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d88782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25402 (p : Pattern) (ha : d11693 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11691 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11692 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11693 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25403 (p : Pattern) (ha : d11702 p = 1) (hb : d85723 p = 1) : d88787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11700 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11643 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11701 q = 1) (hb : d85723 q = 1) : d88786 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d85723, d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11701, d85723, d88786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11702 q = 1) (hb : d85723 q = 1) : d88787 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11702, d88787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25404 (p : Pattern) (ha : d11708 p = 1) (hb : d85724 p = 1) : d88793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11703 q = 1) (hb : d85723 q = 1) : d88788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25403 q ha hb
    | true =>
      simp only [d11703, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11704 q = 1) (hb : d85723 q = 1) : d88789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11704, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11648 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d85724 q = 1) : d88790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11705, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d85724 q = 1) : d88791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d85724 q = 1) : d88792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d85724 q = 1) : d88793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d88793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25405 (p : Pattern) (ha : d11741 p = 1) (hb : d85723 p = 1) : d140568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11739 q = 1) (hb : d85721 q = 1) : d11739 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11740 q = 1) (hb : d85723 q = 1) : d140567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d85723, d140567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11740, d85723, d140567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11741 q = 1) (hb : d85723 q = 1) : d140568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d140568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11741, d140568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25406 (p : Pattern) (ha : d11747 p = 1) (hb : d85724 p = 1) : d140574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11742 q = 1) (hb : d85723 q = 1) : d140569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d140569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25405 q ha hb
    | true =>
      simp only [d11742, d140569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11743 q = 1) (hb : d85723 q = 1) : d140570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d140570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11743, d140570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11744 q = 1) (hb : d85724 q = 1) : d140571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d85724, d140571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11744, d85724, d140571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11745 q = 1) (hb : d85724 q = 1) : d140572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d140572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11745, d140572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11746 q = 1) (hb : d85724 q = 1) : d140573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d140573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11746, d140573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11747 q = 1) (hb : d85724 q = 1) : d140574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d140574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d140574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25407 (p : Pattern) (ha : d85724 p = 1) (hb : d108984 p = 1) : d140580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d85724 q = 1) : d88776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25399 q ha hb
    | true =>
      simp only [d11684, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25400 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d85724 q = 1) : d88777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d85724 q = 1) : d88778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d85724 q = 1) : d88779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d85724 q = 1) : d88783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25401 q ha hb
    | true =>
      simp only [d11694, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25402 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d85724 q = 1) : d88784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d85724 q = 1) : d88785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d85724 q = 1) : d140565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25404 q ha hb
    | true =>
      simp only [d11709, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25386 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108980 q = 1) : d140566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108980, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d85724 q = 1) : d140575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d140575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25406 q ha hb
    | true =>
      simp only [d11748, d140575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d85724 q = 1) : d140576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d140576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d140576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108981 q = 1) : d140577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d140577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d140577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108982 q = 1) : d140578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d140578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108982, d140578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108983 q = 1) : d140579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d140579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108983, d140579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108984 q = 1) : d140580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d140580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108984, d140580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25408 (p : Pattern) (ha : d11754 p = 1) (hb : d85724 p = 1) : d88813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d85724 q = 1) : d88753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d88753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d85724 q = 1) : d88774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d88774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11754 q = 1) (hb : d85724 q = 1) : d88813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11754, d88813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25409 (p : Pattern) (ha : d11755 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11658 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11682 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11755 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25410 (p : Pattern) (ha : d11760 p = 1) (hb : d85724 p = 1) : d88818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11647 q = 1) (hb : d85723 q = 1) : d88750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25385 q ha hb
    | true =>
      simp only [d11647, d88750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11648 q = 1) (hb : d85723 q = 1) : d88751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11648, d88751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11652 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d85724 q = 1) : d88752 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11653, d85724, d88752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d85724 q = 1) : d88780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d88780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d85724 q = 1) : d88781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d88781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11760 q = 1) (hb : d85724 q = 1) : d88818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11760, d88818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25411 (p : Pattern) (ha : d11761 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11651 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25387 q ha hb
    | true =>
      simp only [d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11657 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11657, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11691 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11692 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11761 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25412 (p : Pattern) (ha : d11765 p = 1) (hb : d85724 p = 1) : d88822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d85723 q = 1) : d88788 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25403 q ha hb
    | true =>
      simp only [d11703, d88788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d85723 q = 1) : d88789 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d88789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11648 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11705 q = 1) (hb : d85724 q = 1) : d88790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d85724, d88790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d85724 q = 1) : d88791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11706, d88791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d85724 q = 1) : d88792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d88792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d85724 q = 1) : d88822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d88822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25413 (p : Pattern) (ha : d11771 p = 1) (hb : d85724 p = 1) : d140583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d85723 q = 1) : d140569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d140569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25405 q ha hb
    | true =>
      simp only [d11742, d140569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d85723 q = 1) : d140570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d140570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d140570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11744 q = 1) (hb : d85724 q = 1) : d140571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d85724, d140571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d85724, d140571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11745 q = 1) (hb : d85724 q = 1) : d140572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d140572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11745, d140572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11746 q = 1) (hb : d85724 q = 1) : d140573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d140573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11746, d140573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11771 q = 1) (hb : d85724 q = 1) : d140583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d140583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11771, d140583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25414 (p : Pattern) (ha : d85724 p = 1) (hb : d108989 p = 1) : d140589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d85724 q = 1) : d88776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25399 q ha hb
    | true =>
      simp only [d11684, d88776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25400 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d85724 q = 1) : d88777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d88777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d85724 q = 1) : d88778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d88778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d85724 q = 1) : d88779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d88779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d85724 q = 1) : d88783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25401 q ha hb
    | true =>
      simp only [d11694, d88783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25402 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d85724 q = 1) : d88784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d88784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d85724 q = 1) : d88785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d88785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d85724 q = 1) : d140565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25404 q ha hb
    | true =>
      simp only [d11709, d140565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25386 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108980 q = 1) : d140566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108980, d140566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d85724 q = 1) : d140575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d140575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25406 q ha hb
    | true =>
      simp only [d11748, d140575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d85724 q = 1) : d140576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d140576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d140576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108981 q = 1) : d140577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d140577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d140577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108982 q = 1) : d140578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d140578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108982, d140578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108983 q = 1) : d140579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d140579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108983, d140579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11756 q = 1) (hb : d85724 q = 1) : d88814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25408 q ha hb
    | true =>
      simp only [d11756, d88814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25409 q ha hb
  have h16 (q : Pattern) (ha : d11757 q = 1) (hb : d85724 q = 1) : d88815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d88815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11758 q = 1) (hb : d85724 q = 1) : d88816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11758, d88816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11759 q = 1) (hb : d85724 q = 1) : d88817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d88817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11762 q = 1) (hb : d85724 q = 1) : d88819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25410 q ha hb
    | true =>
      simp only [d11762, d88819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25411 q ha hb
  have h20 (q : Pattern) (ha : d11763 q = 1) (hb : d85724 q = 1) : d88820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d88820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11764 q = 1) (hb : d85724 q = 1) : d88821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11764, d88821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11766 q = 1) (hb : d85724 q = 1) : d140581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25412 q ha hb
    | true =>
      simp only [d11766, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25390 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108985 q = 1) : d140582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108985, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d11772 q = 1) (hb : d85724 q = 1) : d140584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d140584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25413 q ha hb
    | true =>
      simp only [d11772, d140584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11773 q = 1) (hb : d85724 q = 1) : d140585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d140585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11773, d140585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108986 q = 1) : d140586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d140586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108986, d140586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108987 q = 1) : d140587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d140587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108987, d140587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108988 q = 1) : d140588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d140588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108988, d140588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108989 q = 1) : d140589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d140589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108989, d140589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25415 (p : Pattern) (ha : d85724 p = 1) (hb : d108996 p = 1) : d140598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d85724 q = 1) : d140581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25412 q ha hb
    | true =>
      simp only [d11766, d140581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25390 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108985 q = 1) : d140582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108985, d140582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11772 q = 1) (hb : d85724 q = 1) : d140584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d140584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25413 q ha hb
    | true =>
      simp only [d11772, d140584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11773 q = 1) (hb : d85724 q = 1) : d140585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d140585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11773, d140585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108986 q = 1) : d140586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d140586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108986, d140586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108994 q = 1) : d140596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d140596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108994, d140596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108995 q = 1) : d140597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d140597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108995, d140597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108996 q = 1) : d140598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d140598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108996, d140598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25416 (p : Pattern) (ha : d11817 p = 1) (hb : d85723 p = 1) : d88851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11815 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11816 q = 1) (hb : d85723 q = 1) : d88850 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d85723, d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11816, d85723, d88850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11817 q = 1) (hb : d85723 q = 1) : d88851 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11817, d88851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25417 (p : Pattern) (ha : d11828 p = 1) (hb : d85724 p = 1) : d88857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d85723 q = 1) : d88852 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25416 q ha hb
    | true =>
      simp only [d11818, d88852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d85723 q = 1) : d88853 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d88853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11824 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11825 q = 1) (hb : d85724 q = 1) : d88854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d85724, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d85724, d88854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d85724 q = 1) : d88855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11826, d88855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d85724 q = 1) : d88856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d88856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d85724 q = 1) : d88857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d88857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25418 (p : Pattern) (ha : d11822 p = 1) (hb : d85723 p = 1) : d88873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11820 q = 1) (hb : d85721 q = 1) : d11820 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11821 q = 1) (hb : d85723 q = 1) : d88872 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d85723, d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11821, d85723, d88872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11822 q = 1) (hb : d85723 q = 1) : d88873 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11822, d88873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25419 (p : Pattern) (ha : d11836 p = 1) (hb : d85724 p = 1) : d88879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d85723 q = 1) : d88874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25418 q ha hb
    | true =>
      simp only [d11823, d88874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d85723 q = 1) : d88875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d88875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11833 q = 1) (hb : d85724 q = 1) : d88876 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d85724, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d85724, d88876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11834 q = 1) (hb : d85724 q = 1) : d88877 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11834, d88877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11835 q = 1) (hb : d85724 q = 1) : d88878 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11835, d88878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11836 q = 1) (hb : d85724 q = 1) : d88879 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11836, d88879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25420 (p : Pattern) (ha : d11869 p = 1) (hb : d85723 p = 1) : d140607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11815 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11867 q = 1) (hb : d85721 q = 1) : d11867 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11868 q = 1) (hb : d85723 q = 1) : d140606 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d85723, d140606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11868, d85723, d140606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11869 q = 1) (hb : d85723 q = 1) : d140607 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d140607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11869, d140607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25421 (p : Pattern) (ha : d11875 p = 1) (hb : d85724 p = 1) : d140613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d85723 q = 1) : d140608 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d140608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25420 q ha hb
    | true =>
      simp only [d11870, d140608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d85723 q = 1) : d140609 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d140609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d140609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11872 q = 1) (hb : d85724 q = 1) : d140610 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d85724, d140610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d85724, d140610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11873 q = 1) (hb : d85724 q = 1) : d140611 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d140611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11873, d140611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11874 q = 1) (hb : d85724 q = 1) : d140612 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d140612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11874, d140612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11875 q = 1) (hb : d85724 q = 1) : d140613 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d140613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11875, d140613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25422 (p : Pattern) (ha : d85724 p = 1) (hb : d109006 p = 1) : d140619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d85724 q = 1) : d140604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d140604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25417 q ha hb
    | true =>
      simp only [d11837, d140604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25419 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109002 q = 1) : d140605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d140605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d140605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d11876 q = 1) (hb : d85724 q = 1) : d140614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d140614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25421 q ha hb
    | true =>
      simp only [d11876, d140614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11877 q = 1) (hb : d85724 q = 1) : d140615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d140615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11877, d140615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109003 q = 1) : d140616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d140616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109003, d140616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109004 q = 1) : d140617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d140617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109004, d140617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109005 q = 1) : d140618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d140618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109005, d140618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109006 q = 1) : d140619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d140619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109006, d140619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25423 (p : Pattern) (ha : d85724 p = 1) (hb : d109012 p = 1) : d140625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d85724 q = 1) : d88762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d88762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25389 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d85724 q = 1) : d88763 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d88763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d85724 q = 1) : d88771 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25389 q ha hb
    | true =>
      simp only [d11677, d88771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25392 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d85724 q = 1) : d88772 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d88772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d85724 q = 1) : d88773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d88773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108990 q = 1) : d140590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d140590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25407 q ha hb
    | true =>
      simp only [d108990, d140590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25414 q ha hb
  have h7 (q : Pattern) (ha : d11791 q = 1) (hb : d85724 q = 1) : d140592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d140592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25393 q ha hb
    | true =>
      simp only [d11791, d140592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25394 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108991 q = 1) : d140593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d140593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108991, d140593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108992 q = 1) : d140594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d140594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108992, d140594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108993 q = 1) : d140595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d140595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108993, d140595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108997 q = 1) : d140599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d140599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108997, d140599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25415 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25395 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108998 q = 1) : d140600 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d140600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108998, d140600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108999 q = 1) : d140601 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d140601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108999, d140601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109000 q = 1) : d140602 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d140602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109000, d140602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d109001 q = 1) : d140603 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d140603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109001, d140603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d109007 q = 1) : d140620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d140620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109007, d140620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25422 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25398 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d109008 q = 1) : d140621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d140621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109008, d140621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d109009 q = 1) : d140622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d140622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109009, d140622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d109010 q = 1) : d140623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d140623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109010, d140623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d109011 q = 1) : d140624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d140624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109011, d140624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d109012 q = 1) : d140625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d140625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109012, d140625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25424 (p : Pattern) (ha : d85724 p = 1) (hb : d109018 p = 1) : d140631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109013 q = 1) : d140626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d140626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109013, d140626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25423 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109014 q = 1) : d140627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d140627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109014, d140627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109015 q = 1) : d140628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d140628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109015, d140628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109016 q = 1) : d140629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d140629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109016, d140629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109017 q = 1) : d140630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d140630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109017, d140630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109018 q = 1) : d140631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d140631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109018, d140631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25425 (p : Pattern) (ha : d11918 p = 1) (hb : d85723 p = 1) : d88903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11915 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11916 q = 1) (hb : d85721 q = 1) : d11916 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11917 q = 1) (hb : d85723 q = 1) : d88902 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d85723, d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11917, d85723, d88902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11918 q = 1) (hb : d85723 q = 1) : d88903 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11918, d88903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25426 (p : Pattern) (ha : d11928 p = 1) (hb : d85724 p = 1) : d88909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d85724 q = 1) : d88908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11928 q = 1) (hb : d85724 q = 1) : d88909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d88909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25427 (p : Pattern) (ha : d11922 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11916 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11921 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11921, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11921, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11922 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25428 (p : Pattern) (ha : d11932 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11930 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11931 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11932 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25429 (p : Pattern) (ha : d11938 p = 1) (hb : d85724 p = 1) : d88915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25426 q ha hb
    | true =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25428 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d85724 q = 1) : d88911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d85724 q = 1) : d88912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d85724 q = 1) : d88913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d85724 q = 1) : d88914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11938 q = 1) (hb : d85724 q = 1) : d88915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d88915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25430 (p : Pattern) (ha : d11941 p = 1) (hb : d85724 p = 1) : d88918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11927 q = 1) (hb : d85724 q = 1) : d88908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11927, d88908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11941 q = 1) (hb : d85724 q = 1) : d88918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11941, d88918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25431 (p : Pattern) (ha : d11942 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11930 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11931 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d11942 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25432 (p : Pattern) (ha : d11948 p = 1) (hb : d85724 p = 1) : d88924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25426 q ha hb
    | true =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25428 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d85724 q = 1) : d88911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d85724 q = 1) : d88912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d85724 q = 1) : d88913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d85724 q = 1) : d88914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11943 q = 1) (hb : d85724 q = 1) : d88919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25430 q ha hb
    | true =>
      simp only [d11943, d88919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25431 q ha hb
  have h7 (q : Pattern) (ha : d11944 q = 1) (hb : d85724 q = 1) : d88920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d88920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11945 q = 1) (hb : d85724 q = 1) : d88921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11945, d88921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11946 q = 1) (hb : d85724 q = 1) : d88922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d88922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11947 q = 1) (hb : d85724 q = 1) : d88923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d88923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11948 q = 1) (hb : d85724 q = 1) : d88924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11948, d88924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25433 (p : Pattern) (ha : d12056 p = 1) (hb : d85724 p = 1) : d140662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11933 q = 1) (hb : d85724 q = 1) : d88910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25426 q ha hb
    | true =>
      simp only [d11933, d88910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25428 q ha hb
  have h2 (q : Pattern) (ha : d11934 q = 1) (hb : d85724 q = 1) : d88911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d88911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11935 q = 1) (hb : d85724 q = 1) : d88912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11935, d88912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11936 q = 1) (hb : d85724 q = 1) : d88913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d88913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11937 q = 1) (hb : d85724 q = 1) : d88914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d88914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25428 q ha hb
    | true =>
      simp only [d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12056 q = 1) (hb : d85724 q = 1) : d140662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d140662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12056, d140662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25434 (p : Pattern) (ha : d12062 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12051 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25428 q ha hb
    | true =>
      simp only [d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12052 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12053 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12054 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12055 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12057 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25431 q ha hb
    | true =>
      simp only [d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12058 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12059 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12060 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12061 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12062 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25435 (p : Pattern) (ha : d12071 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12057 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25431 q ha hb
    | true =>
      simp only [d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12058 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12059 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12060 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12061 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12071 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25436 (p : Pattern) (ha : d12102 p = 1) (hb : d85723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12101 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12101, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12101, d85723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12102 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25437 (p : Pattern) (ha : d12158 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12103 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25436 q ha hb
    | true =>
      simp only [d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12104 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12155 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12155, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12155, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12156 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12157 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12158 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25438 (p : Pattern) (ha : d12164 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12159 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25437 q ha hb
    | true =>
      simp only [d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12160 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12161 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12162 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12163 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12164 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25439 (p : Pattern) (ha : d11953 p = 1) (hb : d85724 p = 1) : d88929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d85724 q = 1) : d88928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11953 q = 1) (hb : d85724 q = 1) : d88929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d88929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25440 (p : Pattern) (ha : d11955 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11930 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11954 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11955 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25441 (p : Pattern) (ha : d11962 p = 1) (hb : d85724 p = 1) : d88936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d85724 q = 1) : d88934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d85724 q = 1) : d88935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11962 q = 1) (hb : d85724 q = 1) : d88936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d88936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25442 (p : Pattern) (ha : d11965 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11963 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11964 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11965 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25443 (p : Pattern) (ha : d11974 p = 1) (hb : d85723 p = 1) : d88941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11915 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11973 q = 1) (hb : d85723 q = 1) : d88940 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d85723, d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d11973, d85723, d88940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11974 q = 1) (hb : d85723 q = 1) : d88941 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11974, d88941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25444 (p : Pattern) (ha : d11980 p = 1) (hb : d85724 p = 1) : d88947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11975 q = 1) (hb : d85723 q = 1) : d88942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25443 q ha hb
    | true =>
      simp only [d11975, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11976 q = 1) (hb : d85723 q = 1) : d88943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11976, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11920 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d85724 q = 1) : d88944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11977, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d85724 q = 1) : d88945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d85724 q = 1) : d88946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d85724 q = 1) : d88947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d88947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25445 (p : Pattern) (ha : d12013 p = 1) (hb : d85723 p = 1) : d140639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11915 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12011 q = 1) (hb : d85721 q = 1) : d12011 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12012 q = 1) (hb : d85723 q = 1) : d140638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d85723, d140638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12012, d85723, d140638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12013 q = 1) (hb : d85723 q = 1) : d140639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d140639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12013, d140639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25446 (p : Pattern) (ha : d12019 p = 1) (hb : d85724 p = 1) : d140645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12014 q = 1) (hb : d85723 q = 1) : d140640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d140640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25445 q ha hb
    | true =>
      simp only [d12014, d140640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12015 q = 1) (hb : d85723 q = 1) : d140641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d140641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12015, d140641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12016 q = 1) (hb : d85724 q = 1) : d140642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d85724, d140642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12016, d85724, d140642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12017 q = 1) (hb : d85724 q = 1) : d140643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d140643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12017, d140643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12018 q = 1) (hb : d85724 q = 1) : d140644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d140644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12018, d140644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12019 q = 1) (hb : d85724 q = 1) : d140645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d140645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d140645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25447 (p : Pattern) (ha : d85724 p = 1) (hb : d109027 p = 1) : d140651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d85724 q = 1) : d88930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25439 q ha hb
    | true =>
      simp only [d11956, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25440 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d85724 q = 1) : d88931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d85724 q = 1) : d88932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d85724 q = 1) : d88933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d85724 q = 1) : d88937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25441 q ha hb
    | true =>
      simp only [d11966, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25442 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d85724 q = 1) : d88938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d85724 q = 1) : d88939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d85724 q = 1) : d140636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25444 q ha hb
    | true =>
      simp only [d11981, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25426 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109023 q = 1) : d140637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d109023, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d85724 q = 1) : d140646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d140646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25446 q ha hb
    | true =>
      simp only [d12020, d140646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d85724 q = 1) : d140647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d140647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d140647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109024 q = 1) : d140648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d140648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d140648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109025 q = 1) : d140649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d140649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d109025, d140649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109026 q = 1) : d140650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d140650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109026, d140650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109027 q = 1) : d140651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d140651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109027, d140651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25448 (p : Pattern) (ha : d12026 p = 1) (hb : d85724 p = 1) : d88967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11926 q = 1) (hb : d85724 q = 1) : d88907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11926, d88907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11952 q = 1) (hb : d85724 q = 1) : d88928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d88928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12026 q = 1) (hb : d85724 q = 1) : d88967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12026, d88967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25449 (p : Pattern) (ha : d12027 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11930 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11954 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12027 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25450 (p : Pattern) (ha : d12032 p = 1) (hb : d85724 p = 1) : d88972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11919 q = 1) (hb : d85723 q = 1) : d88904 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25425 q ha hb
    | true =>
      simp only [d11919, d88904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11920 q = 1) (hb : d85723 q = 1) : d88905 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11920, d88905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11924 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11925 q = 1) (hb : d85724 q = 1) : d88906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11925, d85724, d88906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d11960 q = 1) (hb : d85724 q = 1) : d88934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d88934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11961 q = 1) (hb : d85724 q = 1) : d88935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11961, d88935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12032 q = 1) (hb : d85724 q = 1) : d88972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12032, d88972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25451 (p : Pattern) (ha : d12033 p = 1) (hb : d85724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11923 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25427 q ha hb
    | true =>
      simp only [d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11929 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11929, d85724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11963 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11964 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12033 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro25452 (p : Pattern) (ha : d12037 p = 1) (hb : d85724 p = 1) : d88976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d85723 q = 1) : d88942 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25443 q ha hb
    | true =>
      simp only [d11975, d88942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d85723 q = 1) : d88943 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d88943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11977 q = 1) (hb : d85724 q = 1) : d88944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d85724, d88944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d85724 q = 1) : d88945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11978, d88945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d85724 q = 1) : d88946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d88946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d85724 q = 1) : d88976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d88976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25453 (p : Pattern) (ha : d12043 p = 1) (hb : d85724 p = 1) : d140654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d85723 q = 1) : d140640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d140640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25445 q ha hb
    | true =>
      simp only [d12014, d140640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d85723 q = 1) : d140641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d140641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d140641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12016 q = 1) (hb : d85724 q = 1) : d140642 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d85724, d140642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d85724, d140642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12017 q = 1) (hb : d85724 q = 1) : d140643 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d140643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12017, d140643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12018 q = 1) (hb : d85724 q = 1) : d140644 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d140644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12018, d140644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12043 q = 1) (hb : d85724 q = 1) : d140654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d140654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12043, d140654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25454 (p : Pattern) (ha : d85724 p = 1) (hb : d109032 p = 1) : d140660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11956 q = 1) (hb : d85724 q = 1) : d88930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25439 q ha hb
    | true =>
      simp only [d11956, d88930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25440 q ha hb
  have h2 (q : Pattern) (ha : d11957 q = 1) (hb : d85724 q = 1) : d88931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d88931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11958 q = 1) (hb : d85724 q = 1) : d88932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11958, d88932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11959 q = 1) (hb : d85724 q = 1) : d88933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d88933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11966 q = 1) (hb : d85724 q = 1) : d88937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25441 q ha hb
    | true =>
      simp only [d11966, d88937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25442 q ha hb
  have h6 (q : Pattern) (ha : d11967 q = 1) (hb : d85724 q = 1) : d88938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d88938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11968 q = 1) (hb : d85724 q = 1) : d88939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11968, d88939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11981 q = 1) (hb : d85724 q = 1) : d140636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25444 q ha hb
    | true =>
      simp only [d11981, d140636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25426 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109023 q = 1) : d140637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d109023, d140637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d12020 q = 1) (hb : d85724 q = 1) : d140646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d140646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25446 q ha hb
    | true =>
      simp only [d12020, d140646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12021 q = 1) (hb : d85724 q = 1) : d140647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d140647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12021, d140647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109024 q = 1) : d140648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d140648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109024, d140648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109025 q = 1) : d140649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d140649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d109025, d140649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109026 q = 1) : d140650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d140650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109026, d140650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12028 q = 1) (hb : d85724 q = 1) : d88968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25448 q ha hb
    | true =>
      simp only [d12028, d88968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25449 q ha hb
  have h16 (q : Pattern) (ha : d12029 q = 1) (hb : d85724 q = 1) : d88969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d88969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12030 q = 1) (hb : d85724 q = 1) : d88970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12030, d88970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12031 q = 1) (hb : d85724 q = 1) : d88971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d88971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12034 q = 1) (hb : d85724 q = 1) : d88973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25450 q ha hb
    | true =>
      simp only [d12034, d88973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25451 q ha hb
  have h20 (q : Pattern) (ha : d12035 q = 1) (hb : d85724 q = 1) : d88974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d88974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12036 q = 1) (hb : d85724 q = 1) : d88975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12036, d88975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12038 q = 1) (hb : d85724 q = 1) : d140652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25452 q ha hb
    | true =>
      simp only [d12038, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25430 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d109028 q = 1) : d140653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d109028, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d12044 q = 1) (hb : d85724 q = 1) : d140655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d140655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25453 q ha hb
    | true =>
      simp only [d12044, d140655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12045 q = 1) (hb : d85724 q = 1) : d140656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d140656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12045, d140656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d109029 q = 1) : d140657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d140657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d109029, d140657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d109030 q = 1) : d140658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d140658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d109030, d140658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d109031 q = 1) : d140659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d140659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d109031, d140659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d109032 q = 1) : d140660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d140660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109032, d140660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25455 (p : Pattern) (ha : d85724 p = 1) (hb : d109039 p = 1) : d140669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d85724 q = 1) : d140652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25452 q ha hb
    | true =>
      simp only [d12038, d140652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25430 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109028 q = 1) : d140653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109028, d140653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12044 q = 1) (hb : d85724 q = 1) : d140655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d140655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25453 q ha hb
    | true =>
      simp only [d12044, d140655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12045 q = 1) (hb : d85724 q = 1) : d140656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d140656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12045, d140656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109029 q = 1) : d140657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d140657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109029, d140657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109037 q = 1) : d140667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d140667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109037, d140667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109038 q = 1) : d140668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d140668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109038, d140668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109039 q = 1) : d140669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d140669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109039, d140669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25456 (p : Pattern) (ha : d12089 p = 1) (hb : d85723 p = 1) : d89005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12087 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12088 q = 1) (hb : d85723 q = 1) : d89004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d85723, d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12088, d85723, d89004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12089 q = 1) (hb : d85723 q = 1) : d89005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12089, d89005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25457 (p : Pattern) (ha : d12100 p = 1) (hb : d85724 p = 1) : d89011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d85723 q = 1) : d89006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25456 q ha hb
    | true =>
      simp only [d12090, d89006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d85723 q = 1) : d89007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d89007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12096 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12097 q = 1) (hb : d85724 q = 1) : d89008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d85724, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d85724, d89008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d85724 q = 1) : d89009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12098, d89009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d85724 q = 1) : d89010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d89010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d85724 q = 1) : d89011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d89011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25458 (p : Pattern) (ha : d12094 p = 1) (hb : d85723 p = 1) : d89027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12092 q = 1) (hb : d85721 q = 1) : d12092 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12093 q = 1) (hb : d85723 q = 1) : d89026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d85723, d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12093, d85723, d89026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12094 q = 1) (hb : d85723 q = 1) : d89027 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12094, d89027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25459 (p : Pattern) (ha : d12108 p = 1) (hb : d85724 p = 1) : d89033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d85723 q = 1) : d89028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25458 q ha hb
    | true =>
      simp only [d12095, d89028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d85723 q = 1) : d89029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d89029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12104 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12105 q = 1) (hb : d85724 q = 1) : d89030 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d85724, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d85724, d89030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12106 q = 1) (hb : d85724 q = 1) : d89031 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12106, d89031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12107 q = 1) (hb : d85724 q = 1) : d89032 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12107, d89032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12108 q = 1) (hb : d85724 q = 1) : d89033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12108, d89033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25460 (p : Pattern) (ha : d12141 p = 1) (hb : d85723 p = 1) : d140678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12139 q = 1) (hb : d85721 q = 1) : d12139 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12140 q = 1) (hb : d85723 q = 1) : d140677 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d85723, d140677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12140, d85723, d140677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12141 q = 1) (hb : d85723 q = 1) : d140678 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d140678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12141, d140678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25461 (p : Pattern) (ha : d12147 p = 1) (hb : d85724 p = 1) : d140684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d85723 q = 1) : d140679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d140679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25460 q ha hb
    | true =>
      simp only [d12142, d140679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d85723 q = 1) : d140680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d140680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d140680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12144 q = 1) (hb : d85724 q = 1) : d140681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d85724, d140681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d85724, d140681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12145 q = 1) (hb : d85724 q = 1) : d140682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d140682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12145, d140682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12146 q = 1) (hb : d85724 q = 1) : d140683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d140683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12146, d140683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d12147 q = 1) (hb : d85724 q = 1) : d140684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d140684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12147, d140684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25462 (p : Pattern) (ha : d85724 p = 1) (hb : d109049 p = 1) : d140690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d85724 q = 1) : d140675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d140675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25457 q ha hb
    | true =>
      simp only [d12109, d140675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25459 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109045 q = 1) : d140676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d140676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d140676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d12148 q = 1) (hb : d85724 q = 1) : d140685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d140685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25461 q ha hb
    | true =>
      simp only [d12148, d140685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12149 q = 1) (hb : d85724 q = 1) : d140686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d140686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12149, d140686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109046 q = 1) : d140687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d140687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109046, d140687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109047 q = 1) : d140688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d140688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109047, d140688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109048 q = 1) : d140689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d140689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109048, d140689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109049 q = 1) : d140690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d140690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109049, d140690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25463 (p : Pattern) (ha : d85724 p = 1) (hb : d109055 p = 1) : d140696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d85724 q = 1) : d88916 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d88916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25429 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d85724 q = 1) : d88917 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d88917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d85724 q = 1) : d88925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25429 q ha hb
    | true =>
      simp only [d11949, d88925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25432 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d85724 q = 1) : d88926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d88926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d85724 q = 1) : d88927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d88927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109033 q = 1) : d140661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d140661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25447 q ha hb
    | true =>
      simp only [d109033, d140661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25454 q ha hb
  have h7 (q : Pattern) (ha : d12063 q = 1) (hb : d85724 q = 1) : d140663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d140663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25433 q ha hb
    | true =>
      simp only [d12063, d140663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25434 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109034 q = 1) : d140664 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d140664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109034, d140664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109035 q = 1) : d140665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d140665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109035, d140665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109036 q = 1) : d140666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d140666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d109036, d140666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109040 q = 1) : d140670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d140670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109040, d140670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25455 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25435 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109041 q = 1) : d140671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d140671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109041, d140671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109042 q = 1) : d140672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d140672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109042, d140672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109043 q = 1) : d140673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d140673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109043, d140673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d109044 q = 1) : d140674 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d140674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109044, d140674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d109050 q = 1) : d140691 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d140691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109050, d140691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25462 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25438 q ha hb
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d109051 q = 1) : d140692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d140692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109051, d140692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d109052 q = 1) : d140693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d140693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109052, d140693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d109053 q = 1) : d140694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d140694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109053, d140694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d85724 q = 1) (hb : d109054 q = 1) : d140695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d140695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109054, d140695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d109055 q = 1) : d140696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d140696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109055, d140696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25464 (p : Pattern) (ha : d85724 p = 1) (hb : d109061 p = 1) : d140702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109056 q = 1) : d140697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d140697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109056, d140697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25463 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109057 q = 1) : d140698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d140698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109057, d140698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109058 q = 1) : d140699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d140699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109058, d140699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109059 q = 1) : d140700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d140700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109059, d140700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109060 q = 1) : d140701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d140701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109060, d140701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109061 q = 1) : d140702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d140702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109061, d140702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25465 (p : Pattern) (ha : d85724 p = 1) (hb : d109067 p = 1) : d140708 p = 1 := by
  have h0 (q : Pattern) (ha : d85724 q = 1) (hb : d108896 q = 1) : d140425 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d140425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25266 q ha hb
    | true =>
      simp only [d108896, d140425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25304 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108936 q = 1) : d140493 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d140493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108936, d140493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25344 q ha hb
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d108937 q = 1) : d140494 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d140494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d140494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d108977 q = 1) : d140562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d140562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108977, d140562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25384 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108978 q = 1) : d140563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d140563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108978, d140563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108979 q = 1) : d140564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d140564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d140564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d109019 q = 1) : d140632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d140632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109019, d140632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25424 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d109020 q = 1) : d140633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d140633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109020, d140633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d109021 q = 1) : d140634 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d140634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109021, d140634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d109022 q = 1) : d140635 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d140635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d140635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d109062 q = 1) : d140703 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d140703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109062, d140703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25464 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d109063 q = 1) : d140704 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d140704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109063, d140704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d109064 q = 1) : d140705 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d140705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109064, d140705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d109065 q = 1) : d140706 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d140706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109065, d140706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d109066 q = 1) : d140707 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d140707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d140707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d109067 q = 1) : d140708 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d140708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d140708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25466 (p : Pattern) (ha : d85724 p = 1) (hb : d109073 p = 1) : d140714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109068 q = 1) : d140709 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d140709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25465 q ha hb
    | true =>
      simp only [d109068, d140709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109069 q = 1) : d140710 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d140710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d140710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109070 q = 1) : d140711 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d140711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d140711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109071 q = 1) : d140712 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d140712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d140712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109072 q = 1) : d140713 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d140713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d140713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109073 q = 1) : d140714 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d140714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d140714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25467 (p : Pattern) (ha : d85724 p = 1) (hb : d109079 p = 1) : d140720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109074 q = 1) : d140715 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d140715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25466 q ha hb
    | true =>
      simp only [d109074, d140715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109075 q = 1) : d140716 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d140716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d140716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109076 q = 1) : d140717 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d140717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d140717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109077 q = 1) : d140718 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d140718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d140718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109078 q = 1) : d140719 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d140719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d140719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109079 q = 1) : d140720 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d140720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d140720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25468 (p : Pattern) (ha : d85724 p = 1) (hb : d109085 p = 1) : d140726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109080 q = 1) : d140721 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d140721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25467 q ha hb
    | true =>
      simp only [d109080, d140721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109081 q = 1) : d140722 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d140722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d140722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109082 q = 1) : d140723 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d140723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d140723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109083 q = 1) : d140724 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d140724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d140724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109084 q = 1) : d140725 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d140725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d140725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109085 q = 1) : d140726 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d140726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d140726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25469 (p : Pattern) (ha : d85724 p = 1) (hb : d109091 p = 1) : d140732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109086 q = 1) : d140727 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d140727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25468 q ha hb
    | true =>
      simp only [d109086, d140727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109087 q = 1) : d140728 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d140728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d140728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109088 q = 1) : d140729 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d140729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d140729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109089 q = 1) : d140730 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d140730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d140730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109090 q = 1) : d140731 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d140731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d140731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109091 q = 1) : d140732 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d140732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d140732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25470 (p : Pattern) (ha : d85724 p = 1) (hb : d109097 p = 1) : d140738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109092 q = 1) : d140733 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d140733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25469 q ha hb
    | true =>
      simp only [d109092, d140733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109093 q = 1) : d140734 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d140734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d140734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109094 q = 1) : d140735 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d140735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d140735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109095 q = 1) : d140736 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d140736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d140736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109096 q = 1) : d140737 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d140737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d140737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109097 q = 1) : d140738 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d140738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d140738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25471 (p : Pattern) (ha : d85724 p = 1) (hb : d109103 p = 1) : d140744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109098 q = 1) : d140739 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d140739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25470 q ha hb
    | true =>
      simp only [d109098, d140739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109099 q = 1) : d140740 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d140740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d140740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109100 q = 1) : d140741 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d140741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d140741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109101 q = 1) : d140742 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d140742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d140742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109102 q = 1) : d140743 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d140743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d140743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109103 q = 1) : d140744 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d140744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d140744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25472 (p : Pattern) (ha : d85724 p = 1) (hb : d109109 p = 1) : d140750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85724 q = 1) (hb : d109104 q = 1) : d140745 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d140745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25471 q ha hb
    | true =>
      simp only [d109104, d140745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d109105 q = 1) : d140746 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d140746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d140746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d85724 q = 1) (hb : d109106 q = 1) : d140747 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d140747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d140747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85724 q = 1) (hb : d109107 q = 1) : d140748 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d140748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d140748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d109108 q = 1) : d140749 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d140749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d140749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d109109 q = 1) : d140750 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d140750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d140750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25473 (p : Pattern) (ha : d78795 p = 1) (hb : d88140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51886 q = 1) (hb : d88139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d78795 q = 1) (hb : d88140 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78795, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78795, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro25474 (p : Pattern) (ha : d78800 p = 1) (hb : d88146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78799 q = 1) (hb : d88145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78799, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78799, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78800 q = 1) (hb : d88146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78800, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78800, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25475 (p : Pattern) (ha : d78806 p = 1) (hb : d88152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78802 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78802, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78803 q = 1) (hb : d88149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78803, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78803, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78804 q = 1) (hb : d88150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78804, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78804, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78805 q = 1) (hb : d88151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78805, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78805, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78806 q = 1) (hb : d88152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78806, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78806, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25476 (p : Pattern) (ha : d78807 p = 1) (hb : d88153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78799 q = 1) (hb : d88145 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78799, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78799, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78807 q = 1) (hb : d88153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78807, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78807, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25477 (p : Pattern) (ha : d78813 p = 1) (hb : d88159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78802 q = 1) (hb : d88148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78802, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78802, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78803 q = 1) (hb : d88149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78803, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78803, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78804 q = 1) (hb : d88150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78804, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78804, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78805 q = 1) (hb : d88151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78805, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78805, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78808 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
    | true =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78809 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78809, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78810 q = 1) (hb : d88156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78810, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78810, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78811 q = 1) (hb : d88157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78811, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78811, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78812 q = 1) (hb : d88158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78812, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78812, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78813 q = 1) (hb : d88159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78813, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78813, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25478 (p : Pattern) (ha : d78818 p = 1) (hb : d88164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78808 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
    | true =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78809 q = 1) (hb : d88155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78809, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78809, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78810 q = 1) (hb : d88156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78810, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78810, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78811 q = 1) (hb : d88157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78811, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78811, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78812 q = 1) (hb : d88158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78812, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78812, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78818 q = 1) (hb : d88164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78818, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78818, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25479 (p : Pattern) (ha : d78824 p = 1) (hb : d88171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d51927 q = 1) (hb : d88170 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d78824 q = 1) (hb : d88171 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78824, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78824, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro25480 (p : Pattern) (ha : d78829 p = 1) (hb : d88177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78825 q = 1) (hb : d88172 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78825, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25479 q ha hb
    | true =>
      simp only [d78825, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78826 q = 1) (hb : d88173 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78826, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78826, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78826 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78826 q = 1) (hb : d88174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78827 q = 1) (hb : d88175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78827, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78827, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78828 q = 1) (hb : d88176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78828, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78828, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78829 q = 1) (hb : d88177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78829, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78829, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25481 (p : Pattern) (ha : d78835 p = 1) (hb : d88183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78830 q = 1) (hb : d88178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78830, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25480 q ha hb
    | true =>
      simp only [d78830, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78831 q = 1) (hb : d88179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78831, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78831, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78832 q = 1) (hb : d88180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78832, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78832, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78833 q = 1) (hb : d88181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78833, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78833, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78834 q = 1) (hb : d88182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78834, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78834, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78835 q = 1) (hb : d88183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78835, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78835, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25482 (p : Pattern) (ha : d78841 p = 1) (hb : d88189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78814 q = 1) (hb : d88160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78814, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25475 q ha hb
    | true =>
      simp only [d78814, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25477 q ha hb
  have h2 (q : Pattern) (ha : d78815 q = 1) (hb : d88161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78815, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78815, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78816 q = 1) (hb : d88162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78816, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78816, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78817 q = 1) (hb : d88163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78817, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78817, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78819 q = 1) (hb : d88165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78819, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78819, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25478 q ha hb
  have h6 (q : Pattern) (ha : d78820 q = 1) (hb : d88166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78820, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78820, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78821 q = 1) (hb : d88167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78821, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78821, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78822 q = 1) (hb : d88168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78822, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78822, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78823 q = 1) (hb : d88169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78823, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78823, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78836 q = 1) (hb : d88184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78836, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78836, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25481 q ha hb
  have h11 (q : Pattern) (ha : d78837 q = 1) (hb : d88185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78837, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d78837, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d78838 q = 1) (hb : d88186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78838, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d78838, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d78839 q = 1) (hb : d88187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d78839, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d78839, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d78840 q = 1) (hb : d88188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d78840, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d78840, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d78841 q = 1) (hb : d88189 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d78841, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d78841, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25483 (p : Pattern) (ha : d78851 p = 1) (hb : d88199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78847 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78848 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78849 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78850 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78851 q = 1) (hb : d88199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78851, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78851, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25484 (p : Pattern) (ha : d78858 p = 1) (hb : d88206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78847 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78848 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78849 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78850 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78808 q = 1) (hb : d88154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
    | true =>
      simp only [d78808, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78854 q = 1) (hb : d88202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78854, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78854, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d78855 q = 1) (hb : d88203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78855, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d78855, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d78856 q = 1) (hb : d88204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78856, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78856, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d78857 q = 1) (hb : d88205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78857, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78857, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d78858 q = 1) (hb : d88206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78858, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78858, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25485 (p : Pattern) (ha : d78903 p = 1) (hb : d88253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78801 q = 1) (hb : d88147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
    | true =>
      simp only [d78801, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78847 q = 1) (hb : d88195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78847, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78848 q = 1) (hb : d88196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78848, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78849 q = 1) (hb : d88197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78849, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78850 q = 1) (hb : d88198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78850, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78903 q = 1) (hb : d88253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d78903, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78903, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25486 (p : Pattern) (ha : d78863 p = 1) (hb : d88211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78862 q = 1) (hb : d88210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78862, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78862, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78863 q = 1) (hb : d88211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78863, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78863, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25487 (p : Pattern) (ha : d78870 p = 1) (hb : d88218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78868 q = 1) (hb : d88216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78868, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78868, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78869 q = 1) (hb : d88217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78869, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78869, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78870 q = 1) (hb : d88218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78870, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78870, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25488 (p : Pattern) (ha : d78874 p = 1) (hb : d88223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10652 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10652, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51999 q = 1) (hb : d88222 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d78874 q = 1) (hb : d88223 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78874, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d78874, d88223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro25489 (p : Pattern) (ha : d78879 p = 1) (hb : d88229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78875 q = 1) (hb : d88224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78875, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25488 q ha hb
    | true =>
      simp only [d78875, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78876 q = 1) (hb : d88225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78876, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78876, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78876 q = 1) (hb : d88226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78877 q = 1) (hb : d88227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78877, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78877, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78878 q = 1) (hb : d88228 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78878, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78878, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78879 q = 1) (hb : d88229 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78879, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78879, d88229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25490 (p : Pattern) (ha : d88235 p = 1) (hb : d140070 p = 1) : d140754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78864 q = 1) (hb : d88212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78864, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25486 q ha hb
    | true =>
      simp only [d78864, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78865 q = 1) (hb : d88213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78865, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78865, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78866 q = 1) (hb : d88214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78866, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78866, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78867 q = 1) (hb : d88215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78867, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78867, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78871 q = 1) (hb : d88219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78871, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25487 q ha hb
    | true =>
      simp only [d78871, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78872 q = 1) (hb : d88220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78872, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78872, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78873 q = 1) (hb : d88221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78873, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78873, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78880 q = 1) (hb : d88230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78880, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25489 q ha hb
    | true =>
      simp only [d78880, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78801 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d78881 q = 1) (hb : d88231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d78881, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d88148 q = 1) : d88148 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d88232 q = 1) (hb : d140067 q = 1) : d140751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88232, d140067, d140751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d88232, d140067, d140751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d88233 q = 1) (hb : d140068 q = 1) : d140752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88233, d140068, d140752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d88233, d140068, d140752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88234 q = 1) (hb : d140069 q = 1) : d140753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88234, d140069, d140753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d88234, d140069, d140753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d88235 q = 1) (hb : d140070 q = 1) : d140754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88235, d140070, d140754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88235, d140070, d140754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25491 (p : Pattern) (ha : d78886 p = 1) (hb : d88236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78798 q = 1) (hb : d88144 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78798, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78862 q = 1) (hb : d88210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78862, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78862, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78886 q = 1) (hb : d88236 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78886, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78886, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25492 (p : Pattern) (ha : d78891 p = 1) (hb : d88241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78796 q = 1) (hb : d88141 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25473 q ha hb
    | true =>
      simp only [d78796, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78797 q = 1) (hb : d88142 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78797, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78797 q = 1) (hb : d88143 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78868 q = 1) (hb : d88216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78868, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78868, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d78869 q = 1) (hb : d88217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78869, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78869, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78891 q = 1) (hb : d88241 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78891, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78891, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25493 (p : Pattern) (ha : d78895 p = 1) (hb : d88245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78875 q = 1) (hb : d88224 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78875, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25488 q ha hb
    | true =>
      simp only [d78875, d88224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78876 q = 1) (hb : d88225 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78876, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78876, d88225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78876 q = 1) (hb : d88226 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78877 q = 1) (hb : d88227 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78877, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78877, d88227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78878 q = 1) (hb : d88228 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78878, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78878, d88228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78895 q = 1) (hb : d88245 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78895, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78895, d88245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25494 (p : Pattern) (ha : d88251 p = 1) (hb : d140074 p = 1) : d140758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78864 q = 1) (hb : d88212 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78864, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25486 q ha hb
    | true =>
      simp only [d78864, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78865 q = 1) (hb : d88213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78865, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78865, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78866 q = 1) (hb : d88214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78866, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78866, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d78867 q = 1) (hb : d88215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78867, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78867, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d78871 q = 1) (hb : d88219 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78871, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25487 q ha hb
    | true =>
      simp only [d78871, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78872 q = 1) (hb : d88220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78872, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78872, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d78873 q = 1) (hb : d88221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78873, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78873, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d78880 q = 1) (hb : d88230 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78880, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25489 q ha hb
    | true =>
      simp only [d78880, d88230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25474 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d78801 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d78881 q = 1) (hb : d88231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78881, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d78881, d88231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1 q = 1) (hb : d88148 q = 1) : d88148 q = 1 := by
    exact hb
  have h12 (q : Pattern) (ha : d88232 q = 1) (hb : d140067 q = 1) : d140751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88232, d140067, d140751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d88232, d140067, d140751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d88233 q = 1) (hb : d140068 q = 1) : d140752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88233, d140068, d140752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d88233, d140068, d140752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88234 q = 1) (hb : d140069 q = 1) : d140753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88234, d140069, d140753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d88234, d140069, d140753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d78887 q = 1) (hb : d88237 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78887, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25491 q ha hb
    | true =>
      simp only [d78887, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d78888 q = 1) (hb : d88238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78888, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78888, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d78889 q = 1) (hb : d88239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78889, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d78889, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d78890 q = 1) (hb : d88240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d78890, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78890, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d78892 q = 1) (hb : d88242 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78892, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25492 q ha hb
    | true =>
      simp only [d78892, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d78893 q = 1) (hb : d88243 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78893, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78893, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d78894 q = 1) (hb : d88244 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d78894, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d78894, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d78896 q = 1) (hb : d88246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78896, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25493 q ha hb
    | true =>
      simp only [d78896, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d78808 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d78897 q = 1) (hb : d88247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d78897, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d88155 q = 1) : d88155 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d88248 q = 1) (hb : d140071 q = 1) : d140755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88248, d140071, d140755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d88248, d140071, d140755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d88249 q = 1) (hb : d140072 q = 1) : d140756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88249, d140072, d140756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d88249, d140072, d140756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d88250 q = 1) (hb : d140073 q = 1) : d140757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88250, d140073, d140757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d88250, d140073, d140757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d88251 q = 1) (hb : d140074 q = 1) : d140758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88251, d140074, d140758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d88251, d140074, d140758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25495 (p : Pattern) (ha : d88260 p = 1) (hb : d140081 p = 1) : d140763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78896 q = 1) (hb : d88246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78896, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25493 q ha hb
    | true =>
      simp only [d78896, d88246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25476 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d78897 q = 1) (hb : d88247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78897, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78897, d88247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d88155 q = 1) : d88155 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d88248 q = 1) (hb : d140071 q = 1) : d140755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88248, d140071, d140755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d88248, d140071, d140755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88258 q = 1) (hb : d140079 q = 1) : d140756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88258, d140079, d140756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88258, d140079, d140756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88259 q = 1) (hb : d140080 q = 1) : d140757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88259, d140080, d140757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88259, d140080, d140757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88260 q = 1) (hb : d140081 q = 1) : d140763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88260, d140081, d140763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88260, d140081, d140763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25496 (p : Pattern) (ha : d78916 p = 1) (hb : d88267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10689 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10689, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52053 q = 1) (hb : d88266 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d88266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d78916 q = 1) (hb : d88267 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d78916, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d78916, d88267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h11 p ha hb
theorem andIntro25497 (p : Pattern) (ha : d78921 p = 1) (hb : d88273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78917 q = 1) (hb : d88268 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78917, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25496 q ha hb
    | true =>
      simp only [d78917, d88268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d78918 q = 1) (hb : d88269 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d78918, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78918, d88269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d78918 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d78918 q = 1) (hb : d88270 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d88270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d78919 q = 1) (hb : d88271 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d78919, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d78919, d88271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d78920 q = 1) (hb : d88272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d78920, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d78920, d88272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d78921 q = 1) (hb : d88273 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d78921, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d78921, d88273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro25498 (p : Pattern) (ha : d88279 p = 1) (hb : d140090 p = 1) : d140772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78922 q = 1) (hb : d88274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d78922, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25497 q ha hb
    | true =>
      simp only [d78922, d88274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25480 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d78830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d78923 q = 1) (hb : d88275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d78923, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78923, d88275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d88179 q = 1) : d88179 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d88276 q = 1) (hb : d140087 q = 1) : d140769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d88276, d140087, d140769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d88276, d140087, d140769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d88277 q = 1) (hb : d140088 q = 1) : d140770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d88277, d140088, d140770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88277, d140088, d140770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88278 q = 1) (hb : d140089 q = 1) : d140771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88278, d140089, d140771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88278, d140089, d140771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88279 q = 1) (hb : d140090 q = 1) : d140772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d88279, d140090, d140772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88279, d140090, d140772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25499 (p : Pattern) (ha : d88285 p = 1) (hb : d140096 p = 1) : d140778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78852 q = 1) (hb : d88200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78852, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d78852, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25483 q ha hb
  have h2 (q : Pattern) (ha : d78853 q = 1) (hb : d88201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78853, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d78853, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d78859 q = 1) (hb : d88207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78859, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25483 q ha hb
    | true =>
      simp only [d78859, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25484 q ha hb
  have h4 (q : Pattern) (ha : d78860 q = 1) (hb : d88208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d78860, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d78860, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d78861 q = 1) (hb : d88209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d78861, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d78861, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88252 q = 1) (hb : d140075 q = 1) : d140759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88252, d140075, d140759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25490 q ha hb
    | true =>
      simp only [d88252, d140075, d140759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25494 q ha hb
  have h7 (q : Pattern) (ha : d78904 q = 1) (hb : d88254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d78904, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25485 q ha hb
    | true =>
      simp only [d78904, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d88255 q = 1) (hb : d140076 q = 1) : d140760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88255, d140076, d140760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88255, d140076, d140760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d88256 q = 1) (hb : d140077 q = 1) : d140761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88256, d140077, d140761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d88256, d140077, d140761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d88257 q = 1) (hb : d140078 q = 1) : d140762 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88257, d140078, d140762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d88257, d140078, d140762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88261 q = 1) (hb : d140082 q = 1) : d140764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88261, d140082, d140764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88261, d140082, d140764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25495 q ha hb
  have h12 (q : Pattern) (ha : d88262 q = 1) (hb : d140083 q = 1) : d140765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88262, d140083, d140765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d88262, d140083, d140765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d88263 q = 1) (hb : d140084 q = 1) : d140766 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88263, d140084, d140766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d88263, d140084, d140766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d88264 q = 1) (hb : d140085 q = 1) : d140767 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88264, d140085, d140767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88264, d140085, d140767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d88265 q = 1) (hb : d140086 q = 1) : d140768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88265, d140086, d140768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88265, d140086, d140768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d88280 q = 1) (hb : d140091 q = 1) : d140773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d88280, d140091, d140773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88280, d140091, d140773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25498 q ha hb
  have h17 (q : Pattern) (ha : d88281 q = 1) (hb : d140092 q = 1) : d140774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d88281, d140092, d140774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d88281, d140092, d140774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d88282 q = 1) (hb : d140093 q = 1) : d140775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d88282, d140093, d140775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d88282, d140093, d140775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d88283 q = 1) (hb : d140094 q = 1) : d140776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d88283, d140094, d140776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d88283, d140094, d140776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d88284 q = 1) (hb : d140095 q = 1) : d140777 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d88284, d140095, d140777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d88284, d140095, d140777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d88285 q = 1) (hb : d140096 q = 1) : d140778 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d88285, d140096, d140778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d88285, d140096, d140778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
end NetHack.Soko22Hazard87
