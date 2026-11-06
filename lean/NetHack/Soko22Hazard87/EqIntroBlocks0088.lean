import NetHack.Soko22Hazard87.EqIntroBlocks0087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro22000 (p : Pattern) (selected : d223170 p = 0) : d224683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223152 q = 0) : d224665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21995 q selected
    | true =>
      simp only [d223152, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21996 q selected
  have h2 (q : Pattern) (selected : d223153 q = 0) : d224666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223153, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223154 q = 0) : d224667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223154, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223160 q = 0) : d224673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223160, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223160, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223169 q = 0) : d224682 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223169, d224682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223169, d224682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223170 q = 0) : d224683 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223170, d224683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223170, d224683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22001 (p : Pattern) (selected : d223176 p = 0) : d224689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223163 q = 0) : d224676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21998 q selected
    | true =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223164 q = 0) : d224677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223171 q = 0) : d224684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223171, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22000 q selected
    | true =>
      simp only [d223171, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223172 q = 0) : d224685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223172, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223172, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223173 q = 0) : d224686 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223173, d224686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223173, d224686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223174 q = 0) : d224687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223174, d224687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223174, d224687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223175 q = 0) : d224688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223175, d224688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223175, d224688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223176 q = 0) : d224689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223176, d224689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223176, d224689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22002 (p : Pattern) (selected : d223184 p = 0) : d224651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117716 q = 0) : d119337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117716, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117716, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
  have h2 (q : Pattern) (selected : d117553 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
    | true =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117717 q = 0) : d119338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117717, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117717, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117554 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117718 q = 0) : d119339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117718, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117718, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117719 q = 0) : d119340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117719, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117719, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223178 q = 0) : d119350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223178, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223178, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21969 q selected
  have h8 (q : Pattern) (selected : d223033 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223033, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21969 q selected
    | true =>
      simp only [d223033, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223179 q = 0) : d119351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223179, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223179, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223034 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223034, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223034, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223180 q = 0) : d119352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223180, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223180, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d223181 q = 0) : d119353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223181, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223181, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223182 q = 0) : d224649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223182, d224649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223182, d224649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117725 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
  have h15 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117726 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d117727 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d117728 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223183 q = 0) : d224650 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223183, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223183, d224650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223184 q = 0) : d224651 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223184, d224651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223184, d224651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22003 (p : Pattern) (selected : d223185 p = 0) : d224660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117720 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
  have h2 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117721 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117722 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117723 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117725 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
  have h8 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117726 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117727 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117728 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117729 q = 0) : d119363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117729, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117729, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117733 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223185 q = 0) : d224660 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223185, d224660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223185, d224660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22004 (p : Pattern) (selected : d223189 p = 0) : d224664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117725 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
  have h2 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117726 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117727 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117728 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117733 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223189 q = 0) : d224664 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223189, d224664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223189, d224664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22005 (p : Pattern) (selected : d223196 p = 0) : d224675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223186 q = 0) : d224661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223186, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22002 q selected
    | true =>
      simp only [d223186, d224661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22003 q selected
  have h2 (q : Pattern) (selected : d223187 q = 0) : d224662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223187, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223187, d224662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223188 q = 0) : d224663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223188, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223188, d224663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223190 q = 0) : d224665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223190, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22003 q selected
    | true =>
      simp only [d223190, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22004 q selected
  have h5 (q : Pattern) (selected : d223191 q = 0) : d224666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223191, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223191, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223192 q = 0) : d224667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223192, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223192, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223193 q = 0) : d224668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223193, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223193, d224668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223194 q = 0) : d224673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223194, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223194, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223195 q = 0) : d224674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223195, d224674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223195, d224674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223196 q = 0) : d224675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223196, d224675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223196, d224675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22006 (p : Pattern) (selected : d223200 p = 0) : d224683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223190 q = 0) : d224665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223190, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22003 q selected
    | true =>
      simp only [d223190, d224665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22004 q selected
  have h2 (q : Pattern) (selected : d223191 q = 0) : d224666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223191, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223191, d224666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223192 q = 0) : d224667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223192, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223192, d224667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223194 q = 0) : d224673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223194, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223194, d224673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223199 q = 0) : d224682 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223199, d224682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223199, d224682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223200 q = 0) : d224683 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223200, d224683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223200, d224683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22007 (p : Pattern) (selected : d223206 p = 0) : d224689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223197 q = 0) : d224676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223197, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22005 q selected
    | true =>
      simp only [d223197, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223198 q = 0) : d224677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223198, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223198, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223201 q = 0) : d224684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223201, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22006 q selected
    | true =>
      simp only [d223201, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223202 q = 0) : d224685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223202, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223202, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223203 q = 0) : d224686 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223203, d224686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223203, d224686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223204 q = 0) : d224687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223204, d224687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223204, d224687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223205 q = 0) : d224688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223205, d224688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223205, d224688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223206 q = 0) : d224689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223206, d224689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223206, d224689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22008 (p : Pattern) (selected : d223210 p = 0) : d224694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223201 q = 0) : d224684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223201, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22006 q selected
    | true =>
      simp only [d223201, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223202 q = 0) : d224685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223202, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223202, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223207 q = 0) : d224691 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223207, d224691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223207, d224691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223208 q = 0) : d224692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223208, d224692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223208, d224692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223209 q = 0) : d224693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223209, d224693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223209, d224693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223210 q = 0) : d224694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223210, d224694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223210, d224694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22009 (p : Pattern) (selected : d223216 p = 0) : d224700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223163 q = 0) : d224676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21998 q selected
    | true =>
      simp only [d223163, d224676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223164 q = 0) : d224677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223164, d224677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223213 q = 0) : d224697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223213, d224697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223213, d224697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223214 q = 0) : d224698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223214, d224698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223214, d224698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223215 q = 0) : d224699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223215, d224699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223215, d224699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223216 q = 0) : d224700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223216, d224700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223216, d224700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22010 (p : Pattern) (selected : d223222 p = 0) : d224706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223177 q = 0) : d224690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223177, d224690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21999 q selected
    | true =>
      simp only [d223177, d224690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22001 q selected
  have h2 (q : Pattern) (selected : d223211 q = 0) : d224695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223211, d224695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22007 q selected
    | true =>
      simp only [d223211, d224695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22008 q selected
  have h3 (q : Pattern) (selected : d223212 q = 0) : d224696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223212, d224696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223212, d224696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223217 q = 0) : d224701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223217, d224701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22009 q selected
    | true =>
      simp only [d223217, d224701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223218 q = 0) : d224702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223218, d224702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223218, d224702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223219 q = 0) : d224703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223219, d224703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223219, d224703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223220 q = 0) : d224704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223220, d224704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223220, d224704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223221 q = 0) : d224705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223221, d224705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223221, d224705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223222 q = 0) : d224706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223222, d224706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223222, d224706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22011 (p : Pattern) (selected : d223227 p = 0) : d224694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223171 q = 0) : d224684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223171, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22000 q selected
    | true =>
      simp only [d223171, d224684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223172 q = 0) : d224685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223172, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223172, d224685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223224 q = 0) : d224691 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223224, d224691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223224, d224691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223225 q = 0) : d224692 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223225, d224692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223225, d224692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223226 q = 0) : d224693 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223226, d224693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223226, d224693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223227 q = 0) : d224694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223227, d224694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223227, d224694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22012 (p : Pattern) (selected : d223233 p = 0) : d224713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223228 q = 0) : d224708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223228, d224708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22011 q selected
    | true =>
      simp only [d223228, d224708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223229 q = 0) : d224709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223229, d224709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223229, d224709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223230 q = 0) : d224710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223230, d224710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223230, d224710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223231 q = 0) : d224711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223231, d224711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223231, d224711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223232 q = 0) : d224712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223232, d224712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223232, d224712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223233 q = 0) : d224713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223233, d224713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223233, d224713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22013 (p : Pattern) (selected : d223239 p = 0) : d224719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d222979 q = 0) : d224529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222979, d224529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222979, d224529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21956 q selected
  have h2 (q : Pattern) (selected : d222980 q = 0) : d224530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222980, d224530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222980, d224530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222989 q = 0) : d224539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222989, d224539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21956 q selected
    | true =>
      simp only [d222989, d224539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21959 q selected
  have h4 (q : Pattern) (selected : d222990 q = 0) : d224540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222990, d224540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222990, d224540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222991 q = 0) : d224541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222991, d224541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222991, d224541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223102 q = 0) : d224615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223102, d224615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21978 q selected
    | true =>
      simp only [d223102, d224615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21987 q selected
  have h7 (q : Pattern) (selected : d223115 q = 0) : d224628 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223115, d224628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21988 q selected
    | true =>
      simp only [d223115, d224628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21989 q selected
  have h8 (q : Pattern) (selected : d223116 q = 0) : d224629 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223116, d224629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223116, d224629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223117 q = 0) : d224630 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223117, d224630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223117, d224630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223118 q = 0) : d224631 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223118, d224631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223118, d224631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223122 q = 0) : d224635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223122, d224635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223122, d224635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21990 q selected
  have h12 (q : Pattern) (selected : d223124 q = 0) : d224637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223124, d224637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223124, d224637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21991 q selected
  have h13 (q : Pattern) (selected : d223125 q = 0) : d224638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223125, d224638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223125, d224638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223126 q = 0) : d224639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223126, d224639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223126, d224639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223127 q = 0) : d224640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223127, d224640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d223127, d224640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d223128 q = 0) : d224641 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223128, d224641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223128, d224641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223223 q = 0) : d224707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223223, d224707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223223, d224707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22010 q selected
  have h18 (q : Pattern) (selected : d223234 q = 0) : d224714 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223234, d224714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223234, d224714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22012 q selected
  have h19 (q : Pattern) (selected : d223235 q = 0) : d224715 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223235, d224715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223235, d224715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223236 q = 0) : d224716 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223236, d224716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223236, d224716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d223237 q = 0) : d224717 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223237, d224717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d223237, d224717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d223238 q = 0) : d224718 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223238, d224718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223238, d224718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223239 q = 0) : d224719 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223239, d224719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223239, d224719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22014 (p : Pattern) (selected : d223245 p = 0) : d224725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223240 q = 0) : d224720 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223240, d224720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223240, d224720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22013 q selected
  have h2 (q : Pattern) (selected : d223241 q = 0) : d224721 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223241, d224721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223241, d224721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223242 q = 0) : d224722 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223242, d224722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223242, d224722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223243 q = 0) : d224723 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223243, d224723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223243, d224723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223244 q = 0) : d224724 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223244, d224724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223244, d224724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223245 q = 0) : d224725 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223245, d224725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223245, d224725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22015 (p : Pattern) (selected : d223251 p = 0) : d224731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117795 q = 0) : d119434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117796 q = 0) : d119435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117886 q = 0) : d119525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117887 q = 0) : d119526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223249 q = 0) : d224729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223249, d224729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223249, d224729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117812 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117813 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223250 q = 0) : d224730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223250, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223250, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223251 q = 0) : d224731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223251, d224731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223251, d224731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22016 (p : Pattern) (selected : d223253 p = 0) : d224733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117799 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117800 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117812 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117813 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223252 q = 0) : d224732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223252, d224732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223252, d224732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117814 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223253 q = 0) : d224733 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223253, d224733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223253, d224733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22017 (p : Pattern) (selected : d223257 p = 0) : d224737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117812 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117813 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117814 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223257 q = 0) : d224737 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223257, d224737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223257, d224737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22018 (p : Pattern) (selected : d223262 p = 0) : d224742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117804 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117805 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117819 q = 0) : d119458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117819, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117819, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223262 q = 0) : d224742 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223262, d224742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223262, d224742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22019 (p : Pattern) (selected : d223268 p = 0) : d224748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223254 q = 0) : d224734 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22015 q selected
    | true =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
  have h2 (q : Pattern) (selected : d223255 q = 0) : d224735 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223256 q = 0) : d224736 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223258 q = 0) : d224738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
    | true =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22017 q selected
  have h5 (q : Pattern) (selected : d223259 q = 0) : d224739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223260 q = 0) : d224740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223261 q = 0) : d224741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223263 q = 0) : d224743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223263, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
    | true =>
      simp only [d223263, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22018 q selected
  have h9 (q : Pattern) (selected : d223264 q = 0) : d224744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223264, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223264, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223265 q = 0) : d224745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223265, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223265, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223266 q = 0) : d224746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223266, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223266, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223267 q = 0) : d224747 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223267, d224747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223267, d224747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223268 q = 0) : d224748 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223268, d224748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223268, d224748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22020 (p : Pattern) (selected : d223272 p = 0) : d224752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223263 q = 0) : d224743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223263, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
    | true =>
      simp only [d223263, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22018 q selected
  have h2 (q : Pattern) (selected : d223264 q = 0) : d224744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223264, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223264, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223265 q = 0) : d224745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223265, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223265, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223266 q = 0) : d224746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223266, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223266, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223271 q = 0) : d224751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223271, d224751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223271, d224751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223272 q = 0) : d224752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223272, d224752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223272, d224752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22021 (p : Pattern) (selected : d223278 p = 0) : d224758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223276 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223277 q = 0) : d224757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223277, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223277, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223278 q = 0) : d224758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223278, d224758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223278, d224758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22022 (p : Pattern) (selected : d223282 p = 0) : d224762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223280 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223281 q = 0) : d224761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223281, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223281, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223282 q = 0) : d224762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223282, d224762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223282, d224762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22023 (p : Pattern) (selected : d223288 p = 0) : d224768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223283 q = 0) : d224763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223283, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22021 q selected
    | true =>
      simp only [d223283, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22022 q selected
  have h2 (q : Pattern) (selected : d223284 q = 0) : d224764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223284, d224764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223284, d224764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223285 q = 0) : d224765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223285, d224765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223285, d224765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223286 q = 0) : d224766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223286, d224766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223286, d224766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223287 q = 0) : d224767 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223287, d224767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223287, d224767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223288 q = 0) : d224768 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223288, d224768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223288, d224768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22024 (p : Pattern) (selected : d223291 p = 0) : d224771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223276 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223277 q = 0) : d224757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223277, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223277, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223291 q = 0) : d224771 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223291, d224771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223291, d224771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22025 (p : Pattern) (selected : d223292 p = 0) : d224772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223280 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223281 q = 0) : d224761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223281, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223281, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223292 q = 0) : d224772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223292, d224772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223292, d224772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22026 (p : Pattern) (selected : d223298 p = 0) : d224778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223283 q = 0) : d224763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223283, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22021 q selected
    | true =>
      simp only [d223283, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22022 q selected
  have h2 (q : Pattern) (selected : d223284 q = 0) : d224764 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223284, d224764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223284, d224764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223285 q = 0) : d224765 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223285, d224765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223285, d224765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223286 q = 0) : d224766 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223286, d224766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223286, d224766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223287 q = 0) : d224767 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223287, d224767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223287, d224767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223293 q = 0) : d224773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223293, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22024 q selected
    | true =>
      simp only [d223293, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22025 q selected
  have h7 (q : Pattern) (selected : d223294 q = 0) : d224774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223294, d224774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223294, d224774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223295 q = 0) : d224775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223295, d224775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223295, d224775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223296 q = 0) : d224776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223296, d224776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223296, d224776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223297 q = 0) : d224777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223297, d224777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223297, d224777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223298 q = 0) : d224778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223298, d224778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223298, d224778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22027 (p : Pattern) (selected : d223303 p = 0) : d224783 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223276 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223302 q = 0) : d224782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223302, d224782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223302, d224782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223303 q = 0) : d224783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223303, d224783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223303, d224783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22028 (p : Pattern) (selected : d223305 p = 0) : d224785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223280 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223304 q = 0) : d224784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223304, d224784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223304, d224784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223305 q = 0) : d224785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223305, d224785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223305, d224785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22029 (p : Pattern) (selected : d223312 p = 0) : d224792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223310 q = 0) : d224790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223310, d224790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223310, d224790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223311 q = 0) : d224791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223311, d224791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223311, d224791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223312 q = 0) : d224792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223312, d224792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223312, d224792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22030 (p : Pattern) (selected : d223315 p = 0) : d224795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223313 q = 0) : d224793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223313, d224793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223313, d224793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223314 q = 0) : d224794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223314, d224794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223314, d224794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223315 q = 0) : d224795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223315, d224795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223315, d224795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22031 (p : Pattern) (selected : d223321 p = 0) : d224801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117876 q = 0) : d119515 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
    | true =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117877 q = 0) : d119516 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117878 q = 0) : d119517 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117878, d119517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117878, d119517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117879 q = 0) : d119518 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117879, d119518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117879, d119518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223319 q = 0) : d224799 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223319, d224799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223319, d224799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117886 q = 0) : d119525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117887 q = 0) : d119526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223320 q = 0) : d224800 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223320, d224800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223320, d224800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223321 q = 0) : d224801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223321, d224801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223321, d224801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22032 (p : Pattern) (selected : d223325 p = 0) : d224805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117886 q = 0) : d119525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117887 q = 0) : d119526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117812 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117813 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223250 q = 0) : d224730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223250, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223250, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117814 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223325 q = 0) : d224805 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223325, d224805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223325, d224805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22033 (p : Pattern) (selected : d223331 p = 0) : d224811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223322 q = 0) : d224802 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223322, d224802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22031 q selected
    | true =>
      simp only [d223322, d224802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22015 q selected
  have h2 (q : Pattern) (selected : d223323 q = 0) : d224803 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223323, d224803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223323, d224803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223324 q = 0) : d224804 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223324, d224804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223324, d224804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223326 q = 0) : d224806 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223326, d224806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22015 q selected
    | true =>
      simp only [d223326, d224806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22032 q selected
  have h5 (q : Pattern) (selected : d223327 q = 0) : d224807 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223327, d224807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223327, d224807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223328 q = 0) : d224808 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223328, d224808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223328, d224808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223329 q = 0) : d224809 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223329, d224809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223329, d224809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223254 q = 0) : d224734 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22015 q selected
    | true =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
  have h9 (q : Pattern) (selected : d223255 q = 0) : d224735 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223256 q = 0) : d224736 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223258 q = 0) : d224738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
    | true =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22017 q selected
  have h12 (q : Pattern) (selected : d223259 q = 0) : d224739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223260 q = 0) : d224740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223261 q = 0) : d224741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223330 q = 0) : d224810 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223330, d224810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223330, d224810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223331 q = 0) : d224811 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223331, d224811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223331, d224811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro22034 (p : Pattern) (selected : d223336 p = 0) : d224816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223254 q = 0) : d224734 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22015 q selected
    | true =>
      simp only [d223254, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
  have h2 (q : Pattern) (selected : d223255 q = 0) : d224735 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223255, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223256 q = 0) : d224736 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223256, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223258 q = 0) : d224738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22016 q selected
    | true =>
      simp only [d223258, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22017 q selected
  have h5 (q : Pattern) (selected : d223259 q = 0) : d224739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223259, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223260 q = 0) : d224740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223260, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223261 q = 0) : d224741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223261, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223334 q = 0) : d224814 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223334, d224814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223334, d224814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223335 q = 0) : d224815 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223335, d224815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223335, d224815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223336 q = 0) : d224816 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223336, d224816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223336, d224816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22035 (p : Pattern) (selected : d223342 p = 0) : d224822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223332 q = 0) : d224812 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223332, d224812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22033 q selected
    | true =>
      simp only [d223332, d224812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223333 q = 0) : d224813 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223333, d224813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223333, d224813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223337 q = 0) : d224817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22034 q selected
    | true =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223338 q = 0) : d224818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223339 q = 0) : d224819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223339, d224819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223339, d224819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223340 q = 0) : d224820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223340, d224820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223340, d224820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223341 q = 0) : d224821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223341, d224821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223341, d224821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223342 q = 0) : d224822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223342, d224822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223342, d224822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22036 (p : Pattern) (selected : d223346 p = 0) : d224826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223337 q = 0) : d224817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22034 q selected
    | true =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223338 q = 0) : d224818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223343 q = 0) : d224823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223343, d224823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223343, d224823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223344 q = 0) : d224824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223344, d224824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223344, d224824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223345 q = 0) : d224825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223345, d224825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223345, d224825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223346 q = 0) : d224826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223346, d224826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223346, d224826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22037 (p : Pattern) (selected : d10188 p = 0) : d101488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10181 q = 0) : d101482 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6731 q selected
  have h2 (q : Pattern) (selected : d10182 q = 0) : d101483 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10182, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10182, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10184 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6732 q selected
    | true =>
      simp only [d10184, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10185 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10185, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10186 q = 0) : d101486 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10186, d101486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10186, d101486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10187 q = 0) : d101487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10187, d101487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10187, d101487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10188 q = 0) : d101488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10188, d101488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10188, d101488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro22038 (p : Pattern) (selected : d223354 p = 0) : d224731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117911 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
    | true =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117912 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117913 q = 0) : d119434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117913, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117913, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117914 q = 0) : d119435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117914, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117914, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223348 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223348, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22037 q selected
    | true =>
      simp only [d223348, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223349 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223349, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223349, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223350 q = 0) : d119525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223350, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223350, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223351 q = 0) : d119526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223351, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223351, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223352 q = 0) : d224729 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223352, d224729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223352, d224729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117930 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117931 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223353 q = 0) : d224730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223353, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223353, d224730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223354 q = 0) : d224731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223354, d224731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223354, d224731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22039 (p : Pattern) (selected : d223356 p = 0) : d224733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117917 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117918 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117930 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117931 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223355 q = 0) : d224732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223355, d224732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223355, d224732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117932 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223356 q = 0) : d224733 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223356, d224733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223356, d224733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22040 (p : Pattern) (selected : d223360 p = 0) : d224737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117930 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117931 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117932 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223360 q = 0) : d224737 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223360, d224737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223360, d224737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22041 (p : Pattern) (selected : d223365 p = 0) : d224742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117922 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117923 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117937 q = 0) : d119458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117937, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117937, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223365 q = 0) : d224742 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223365, d224742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223365, d224742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22042 (p : Pattern) (selected : d223371 p = 0) : d224748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223357 q = 0) : d224734 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223357, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22038 q selected
    | true =>
      simp only [d223357, d224734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22039 q selected
  have h2 (q : Pattern) (selected : d223358 q = 0) : d224735 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223358, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223358, d224735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223359 q = 0) : d224736 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223359, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223359, d224736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223361 q = 0) : d224738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223361, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22039 q selected
    | true =>
      simp only [d223361, d224738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22040 q selected
  have h5 (q : Pattern) (selected : d223362 q = 0) : d224739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223362, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223362, d224739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223363 q = 0) : d224740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223363, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223363, d224740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223364 q = 0) : d224741 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223364, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223364, d224741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223366 q = 0) : d224743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223366, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22039 q selected
    | true =>
      simp only [d223366, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22041 q selected
  have h9 (q : Pattern) (selected : d223367 q = 0) : d224744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223367, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223367, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223368 q = 0) : d224745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223368, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223368, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223369 q = 0) : d224746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223369, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223369, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223370 q = 0) : d224747 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223370, d224747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223370, d224747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223371 q = 0) : d224748 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223371, d224748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223371, d224748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22043 (p : Pattern) (selected : d223375 p = 0) : d224752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223366 q = 0) : d224743 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223366, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22039 q selected
    | true =>
      simp only [d223366, d224743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22041 q selected
  have h2 (q : Pattern) (selected : d223367 q = 0) : d224744 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223367, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223367, d224744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223368 q = 0) : d224745 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223368, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223368, d224745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223369 q = 0) : d224746 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223369, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223369, d224746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223374 q = 0) : d224751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223374, d224751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223374, d224751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223375 q = 0) : d224752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223375, d224752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223375, d224752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22044 (p : Pattern) (selected : d223381 p = 0) : d224758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223372 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223372, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22042 q selected
    | true =>
      simp only [d223372, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223373 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223373, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223373, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223376 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22043 q selected
    | true =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223377 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223378 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223378, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223378, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223379 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223379, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223379, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223380 q = 0) : d224757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223380, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223380, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223381 q = 0) : d224758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223381, d224758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223381, d224758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22045 (p : Pattern) (selected : d223385 p = 0) : d224762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223376 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22043 q selected
    | true =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223377 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223382 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223382, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223382, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223383 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223383, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223383, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223384 q = 0) : d224761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223384, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223384, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223385 q = 0) : d224762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223385, d224762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223385, d224762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22046 (p : Pattern) (selected : d223391 p = 0) : d224832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223388 q = 0) : d224829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223388, d224829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223388, d224829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223389 q = 0) : d224830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223389, d224830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223389, d224830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223390 q = 0) : d224831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223390, d224831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223390, d224831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223391 q = 0) : d224832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223391, d224832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223391, d224832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22047 (p : Pattern) (selected : d223397 p = 0) : d224838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223306 q = 0) : d224786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223306, d224786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22027 q selected
    | true =>
      simp only [d223306, d224786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22028 q selected
  have h2 (q : Pattern) (selected : d223307 q = 0) : d224787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223307, d224787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223307, d224787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223308 q = 0) : d224788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223308, d224788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223308, d224788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223309 q = 0) : d224789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223309, d224789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223309, d224789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223316 q = 0) : d224796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223316, d224796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22029 q selected
    | true =>
      simp only [d223316, d224796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22030 q selected
  have h6 (q : Pattern) (selected : d223317 q = 0) : d224797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223317, d224797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223317, d224797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223318 q = 0) : d224798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223318, d224798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223318, d224798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223347 q = 0) : d224827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223347, d224827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22035 q selected
    | true =>
      simp only [d223347, d224827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22036 q selected
  have h9 (q : Pattern) (selected : d223386 q = 0) : d224763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223386, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22044 q selected
    | true =>
      simp only [d223386, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22045 q selected
  have h10 (q : Pattern) (selected : d223387 q = 0) : d224828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223387, d224828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223387, d224828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223392 q = 0) : d224833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223392, d224833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22046 q selected
    | true =>
      simp only [d223392, d224833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223393 q = 0) : d224834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223393, d224834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223393, d224834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223394 q = 0) : d224835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223394, d224835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223394, d224835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223395 q = 0) : d224836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223395, d224836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223395, d224836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223396 q = 0) : d224837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223396, d224837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223396, d224837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223397 q = 0) : d224838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223397, d224838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223397, d224838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22048 (p : Pattern) (selected : d223398 p = 0) : d224839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223276 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223276, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223302 q = 0) : d224782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223302, d224782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223302, d224782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223398 q = 0) : d224839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223398, d224839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223398, d224839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22049 (p : Pattern) (selected : d223399 p = 0) : d224840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223280 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223280, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223304 q = 0) : d224784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223304, d224784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223304, d224784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223399 q = 0) : d224840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223399, d224840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223399, d224840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22050 (p : Pattern) (selected : d223404 p = 0) : d224845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223275 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223275, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223310 q = 0) : d224790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223310, d224790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223310, d224790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223311 q = 0) : d224791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223311, d224791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223311, d224791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223404 q = 0) : d224845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223404, d224845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223404, d224845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22051 (p : Pattern) (selected : d223405 p = 0) : d224846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223279 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223279, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223313 q = 0) : d224793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223313, d224793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223313, d224793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223314 q = 0) : d224794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223314, d224794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223314, d224794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223405 q = 0) : d224846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223405, d224846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223405, d224846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22052 (p : Pattern) (selected : d223409 p = 0) : d224850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223332 q = 0) : d224812 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223332, d224812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22033 q selected
    | true =>
      simp only [d223332, d224812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223333 q = 0) : d224813 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223333, d224813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223333, d224813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223337 q = 0) : d224817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22034 q selected
    | true =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223338 q = 0) : d224818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223339 q = 0) : d224819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223339, d224819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223339, d224819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223340 q = 0) : d224820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223340, d224820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223340, d224820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223341 q = 0) : d224821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223341, d224821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223341, d224821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223409 q = 0) : d224850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223409, d224850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223409, d224850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22053 (p : Pattern) (selected : d223410 p = 0) : d224851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223337 q = 0) : d224817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22034 q selected
    | true =>
      simp only [d223337, d224817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223338 q = 0) : d224818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223338, d224818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223273 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22020 q selected
    | true =>
      simp only [d223273, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223274 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223274, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223343 q = 0) : d224823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223343, d224823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223343, d224823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223344 q = 0) : d224824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223344, d224824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223344, d224824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223345 q = 0) : d224825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223345, d224825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223345, d224825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223410 q = 0) : d224851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223410, d224851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223410, d224851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22054 (p : Pattern) (selected : d223412 p = 0) : d224771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223372 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223372, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22042 q selected
    | true =>
      simp only [d223372, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223373 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223373, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223373, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223376 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22043 q selected
    | true =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223377 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223378 q = 0) : d224755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223378, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223378, d224755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223379 q = 0) : d224756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223379, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223379, d224756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223380 q = 0) : d224757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223380, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223380, d224757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223412 q = 0) : d224771 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223412, d224771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223412, d224771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22055 (p : Pattern) (selected : d223413 p = 0) : d224772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223376 q = 0) : d224753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22043 q selected
    | true =>
      simp only [d223376, d224753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223377 q = 0) : d224754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, d224754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223382 q = 0) : d224759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223382, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223382, d224759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223383 q = 0) : d224760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223383, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223383, d224760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223384 q = 0) : d224761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223384, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223384, d224761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223413 q = 0) : d224772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223413, d224772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223413, d224772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22056 (p : Pattern) (selected : d223416 p = 0) : d224854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223269 q = 0) : d224749 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22019 q selected
    | true =>
      simp only [d223269, d224749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223270 q = 0) : d224750 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223270, d224750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223388 q = 0) : d224829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223388, d224829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223388, d224829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223389 q = 0) : d224830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223389, d224830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223389, d224830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223390 q = 0) : d224831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223390, d224831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223390, d224831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223416 q = 0) : d224854 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223416, d224854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223416, d224854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22057 (p : Pattern) (selected : d223422 p = 0) : d224860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223306 q = 0) : d224786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223306, d224786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22027 q selected
    | true =>
      simp only [d223306, d224786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22028 q selected
  have h2 (q : Pattern) (selected : d223307 q = 0) : d224787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223307, d224787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223307, d224787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223308 q = 0) : d224788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223308, d224788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223308, d224788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223309 q = 0) : d224789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223309, d224789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223309, d224789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223316 q = 0) : d224796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223316, d224796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22029 q selected
    | true =>
      simp only [d223316, d224796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22030 q selected
  have h6 (q : Pattern) (selected : d223317 q = 0) : d224797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223317, d224797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223317, d224797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223318 q = 0) : d224798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223318, d224798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223318, d224798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223347 q = 0) : d224827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223347, d224827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22035 q selected
    | true =>
      simp only [d223347, d224827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22036 q selected
  have h9 (q : Pattern) (selected : d223386 q = 0) : d224763 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223386, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22044 q selected
    | true =>
      simp only [d223386, d224763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22045 q selected
  have h10 (q : Pattern) (selected : d223387 q = 0) : d224828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223387, d224828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223387, d224828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223392 q = 0) : d224833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223392, d224833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22046 q selected
    | true =>
      simp only [d223392, d224833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223393 q = 0) : d224834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223393, d224834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223393, d224834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223394 q = 0) : d224835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223394, d224835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223394, d224835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223395 q = 0) : d224836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223395, d224836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223395, d224836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223396 q = 0) : d224837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223396, d224837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223396, d224837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223400 q = 0) : d224841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223400, d224841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22048 q selected
    | true =>
      simp only [d223400, d224841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22049 q selected
  have h17 (q : Pattern) (selected : d223401 q = 0) : d224842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223401, d224842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223401, d224842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223402 q = 0) : d224843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223402, d224843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223402, d224843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d223403 q = 0) : d224844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223403, d224844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223403, d224844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223406 q = 0) : d224847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223406, d224847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22050 q selected
    | true =>
      simp only [d223406, d224847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22051 q selected
  have h21 (q : Pattern) (selected : d223407 q = 0) : d224848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223407, d224848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223407, d224848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d223408 q = 0) : d224849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223408, d224849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223408, d224849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223411 q = 0) : d224852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223411, d224852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22052 q selected
    | true =>
      simp only [d223411, d224852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22053 q selected
  have h24 (q : Pattern) (selected : d223414 q = 0) : d224773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223414, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22054 q selected
    | true =>
      simp only [d223414, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22055 q selected
  have h25 (q : Pattern) (selected : d223415 q = 0) : d224853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223415, d224853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d223415, d224853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d223417 q = 0) : d224855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223417, d224855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22056 q selected
    | true =>
      simp only [d223417, d224855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d223418 q = 0) : d224856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223418, d224856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d223418, d224856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d223419 q = 0) : d224857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223419, d224857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d223419, d224857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d223420 q = 0) : d224858 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223420, d224858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d223420, d224858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d223421 q = 0) : d224859 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223421, d224859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223421, d224859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d223422 q = 0) : d224860 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223422, d224860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223422, d224860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22058 (p : Pattern) (selected : d223434 p = 0) : d224872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223424 q = 0) : d224862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223424, d224862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22036 q selected
    | true =>
      simp only [d223424, d224862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22022 q selected
  have h2 (q : Pattern) (selected : d223425 q = 0) : d224863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223425, d224863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223425, d224863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223426 q = 0) : d224864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223426, d224864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223426, d224864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223427 q = 0) : d224865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223427, d224865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223427, d224865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223428 q = 0) : d224866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223428, d224866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223428, d224866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223429 q = 0) : d224867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223429, d224867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22022 q selected
    | true =>
      simp only [d223429, d224867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223430 q = 0) : d224868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223430, d224868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223430, d224868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223431 q = 0) : d224869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223431, d224869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223431, d224869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223432 q = 0) : d224870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223432, d224870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223432, d224870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223433 q = 0) : d224871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223433, d224871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223433, d224871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223434 q = 0) : d224872 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223434, d224872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223434, d224872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22059 (p : Pattern) (selected : d223440 p = 0) : d224878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223429 q = 0) : d224867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223429, d224867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22022 q selected
    | true =>
      simp only [d223429, d224867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223430 q = 0) : d224868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223430, d224868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223430, d224868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223431 q = 0) : d224869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223431, d224869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223431, d224869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223432 q = 0) : d224870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223432, d224870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223432, d224870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223433 q = 0) : d224871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223433, d224871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223433, d224871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223435 q = 0) : d224873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223435, d224873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22025 q selected
    | true =>
      simp only [d223435, d224873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223436 q = 0) : d224874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223436, d224874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223436, d224874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223437 q = 0) : d224875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223437, d224875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223437, d224875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223438 q = 0) : d224876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223438, d224876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223438, d224876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223439 q = 0) : d224877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223439, d224877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223439, d224877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223440 q = 0) : d224878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223440, d224878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223440, d224878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22060 (p : Pattern) (selected : d223447 p = 0) : d224885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223411 q = 0) : d224852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223411, d224852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22052 q selected
    | true =>
      simp only [d223411, d224852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22053 q selected
  have h2 (q : Pattern) (selected : d223414 q = 0) : d224773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223414, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22054 q selected
    | true =>
      simp only [d223414, d224773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22055 q selected
  have h3 (q : Pattern) (selected : d223415 q = 0) : d224853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223415, d224853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223415, d224853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223417 q = 0) : d224855 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223417, d224855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22056 q selected
    | true =>
      simp only [d223417, d224855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223418 q = 0) : d224856 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223418, d224856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223418, d224856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223419 q = 0) : d224857 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223419, d224857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223419, d224857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223445 q = 0) : d224883 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223445, d224883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223445, d224883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223446 q = 0) : d224884 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223446, d224884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223446, d224884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223447 q = 0) : d224885 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223447, d224885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223447, d224885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22061 (p : Pattern) (selected : d223449 p = 0) : d224887 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223435 q = 0) : d224873 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223435, d224873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22025 q selected
    | true =>
      simp only [d223435, d224873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223436 q = 0) : d224874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223436, d224874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223436, d224874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223437 q = 0) : d224875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223437, d224875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223437, d224875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223438 q = 0) : d224876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223438, d224876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223438, d224876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223439 q = 0) : d224877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223439, d224877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223439, d224877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223449 q = 0) : d224887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223449, d224887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223449, d224887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22062 (p : Pattern) (selected : d223457 p = 0) : d224895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118027 q = 0) : d119615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118027, d119615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118027, d119615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
  have h2 (q : Pattern) (selected : d117876 q = 0) : d119515 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
    | true =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118028 q = 0) : d119616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118028, d119616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118028, d119616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117877 q = 0) : d119516 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118029 q = 0) : d119617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118029, d119617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118029, d119617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118030 q = 0) : d119618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118030, d119618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118030, d119618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223455 q = 0) : d224893 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223455, d224893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223455, d224893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118044 q = 0) : d119632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
  have h9 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118045 q = 0) : d119633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118046 q = 0) : d119634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118047 q = 0) : d119635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223456 q = 0) : d224894 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223456, d224894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223456, d224894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223457 q = 0) : d224895 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223457, d224895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223457, d224895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22063 (p : Pattern) (selected : d223460 p = 0) : d224898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118031 q = 0) : d119619 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
  have h2 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118032 q = 0) : d119620 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118033 q = 0) : d119621 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118034 q = 0) : d119622 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118044 q = 0) : d119632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
  have h8 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118045 q = 0) : d119633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118046 q = 0) : d119634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118047 q = 0) : d119635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223458 q = 0) : d224896 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223458, d224896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223458, d224896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118061 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
  have h15 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d118062 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d118063 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d118064 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223459 q = 0) : d224897 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223459, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223459, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223460 q = 0) : d224898 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223460, d224898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223460, d224898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22064 (p : Pattern) (selected : d223464 p = 0) : d224902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118044 q = 0) : d119632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
  have h2 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118045 q = 0) : d119633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118046 q = 0) : d119634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118047 q = 0) : d119635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118061 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
  have h8 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118062 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118063 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118064 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223459 q = 0) : d224897 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223459, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223459, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118065 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223464 q = 0) : d224902 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223464, d224902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223464, d224902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22065 (p : Pattern) (selected : d223470 p = 0) : d224908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118036 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
  have h2 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118037 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118038 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118039 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118061 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
  have h8 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118062 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118063 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118064 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223469 q = 0) : d224907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223469, d224907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223469, d224907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118065 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223470 q = 0) : d224908 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223470, d224908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223470, d224908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22066 (p : Pattern) (selected : d223474 p = 0) : d224912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118061 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
  have h2 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118062 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118063 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118064 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118065 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223474 q = 0) : d224912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223474, d224912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223474, d224912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22067 (p : Pattern) (selected : d223480 p = 0) : d224918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223461 q = 0) : d224899 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223461, d224899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22062 q selected
    | true =>
      simp only [d223461, d224899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22063 q selected
  have h2 (q : Pattern) (selected : d223462 q = 0) : d224900 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223462, d224900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223462, d224900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223463 q = 0) : d224901 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223463, d224901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223463, d224901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223465 q = 0) : d224903 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223465, d224903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22063 q selected
    | true =>
      simp only [d223465, d224903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22064 q selected
  have h5 (q : Pattern) (selected : d223466 q = 0) : d224904 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223466, d224904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223466, d224904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223467 q = 0) : d224905 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223467, d224905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223467, d224905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223468 q = 0) : d224906 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223468, d224906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223468, d224906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223471 q = 0) : d224909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22063 q selected
    | true =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
  have h9 (q : Pattern) (selected : d223472 q = 0) : d224910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223473 q = 0) : d224911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223475 q = 0) : d224913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
    | true =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22066 q selected
  have h12 (q : Pattern) (selected : d223476 q = 0) : d224914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223477 q = 0) : d224915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223478 q = 0) : d224916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223479 q = 0) : d224917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223479, d224917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223479, d224917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223480 q = 0) : d224918 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223480, d224918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223480, d224918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro22068 (p : Pattern) (selected : d223485 p = 0) : d224923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223471 q = 0) : d224909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22063 q selected
    | true =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
  have h2 (q : Pattern) (selected : d223472 q = 0) : d224910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223473 q = 0) : d224911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223475 q = 0) : d224913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
    | true =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22066 q selected
  have h5 (q : Pattern) (selected : d223476 q = 0) : d224914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223477 q = 0) : d224915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223478 q = 0) : d224916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223483 q = 0) : d224921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223483, d224921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223483, d224921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223484 q = 0) : d224922 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223484, d224922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223484, d224922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223485 q = 0) : d224923 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223485, d224923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223485, d224923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22069 (p : Pattern) (selected : d223491 p = 0) : d224929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223481 q = 0) : d224919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223481, d224919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22067 q selected
    | true =>
      simp only [d223481, d224919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223482 q = 0) : d224920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223482, d224920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223482, d224920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223486 q = 0) : d224924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223486, d224924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22068 q selected
    | true =>
      simp only [d223486, d224924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223487 q = 0) : d224925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223487, d224925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223487, d224925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223488 q = 0) : d224926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223488, d224926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223488, d224926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223489 q = 0) : d224927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223489, d224927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223489, d224927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223490 q = 0) : d224928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223490, d224928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223490, d224928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223491 q = 0) : d224929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223491, d224929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223491, d224929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22070 (p : Pattern) (selected : d223492 p = 0) : d224930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118053 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
  have h2 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118054 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118055 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118056 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118083 q = 0) : d119671 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118083, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118083, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223492 q = 0) : d224930 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223492, d224930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223492, d224930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22071 (p : Pattern) (selected : d223498 p = 0) : d224936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223493 q = 0) : d224931 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223493, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
    | true =>
      simp only [d223493, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22070 q selected
  have h2 (q : Pattern) (selected : d223494 q = 0) : d224932 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223494, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223494, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223495 q = 0) : d224933 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223495, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223495, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223496 q = 0) : d224934 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223496, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223496, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223497 q = 0) : d224935 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223497, d224935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223497, d224935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223498 q = 0) : d224936 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223498, d224936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223498, d224936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22072 (p : Pattern) (selected : d223504 p = 0) : d224942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223486 q = 0) : d224924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223486, d224924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22068 q selected
    | true =>
      simp only [d223486, d224924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223487 q = 0) : d224925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223487, d224925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223487, d224925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223499 q = 0) : d224937 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223499, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22071 q selected
    | true =>
      simp only [d223499, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223500 q = 0) : d224938 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223500, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223500, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223501 q = 0) : d224939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223501, d224939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223501, d224939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223502 q = 0) : d224940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223502, d224940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223502, d224940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223503 q = 0) : d224941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223503, d224941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223503, d224941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223504 q = 0) : d224942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223504, d224942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223504, d224942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22073 (p : Pattern) (selected : d223512 p = 0) : d224898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118097 q = 0) : d119619 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118097, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118097, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
  have h2 (q : Pattern) (selected : d117911 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
    | true =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118098 q = 0) : d119620 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118098, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118098, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117912 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118099 q = 0) : d119621 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118099, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118099, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118100 q = 0) : d119622 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118100, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118100, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223506 q = 0) : d119632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223506, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223506, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22037 q selected
  have h8 (q : Pattern) (selected : d223348 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223348, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22037 q selected
    | true =>
      simp only [d223348, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223507 q = 0) : d119633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223507, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223507, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223349 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223349, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223349, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223508 q = 0) : d119634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223508, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223508, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d223509 q = 0) : d119635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223509, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223509, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223510 q = 0) : d224896 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223510, d224896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223510, d224896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118114 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
  have h15 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d118115 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d118116 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d118117 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223511 q = 0) : d224897 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223511, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223511, d224897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223512 q = 0) : d224898 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223512, d224898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223512, d224898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22074 (p : Pattern) (selected : d223514 p = 0) : d224908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118101 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
  have h2 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118102 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118103 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118104 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118114 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
  have h8 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118115 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118116 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118117 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223513 q = 0) : d224907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223513, d224907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223513, d224907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118118 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223514 q = 0) : d224908 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223514, d224908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223514, d224908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22075 (p : Pattern) (selected : d223518 p = 0) : d224912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118114 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
  have h2 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118115 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118116 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118117 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118118 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223518 q = 0) : d224912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223518, d224912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223518, d224912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22076 (p : Pattern) (selected : d223523 p = 0) : d224930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118106 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
  have h2 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118107 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118108 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118109 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118123 q = 0) : d119671 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118123, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118123, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223523 q = 0) : d224930 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223523, d224930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223523, d224930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22077 (p : Pattern) (selected : d223529 p = 0) : d224945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223515 q = 0) : d224909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223515, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22073 q selected
    | true =>
      simp only [d223515, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22074 q selected
  have h2 (q : Pattern) (selected : d223516 q = 0) : d224910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223516, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223516, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223517 q = 0) : d224911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223517, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223517, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223519 q = 0) : d224913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223519, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22074 q selected
    | true =>
      simp only [d223519, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22075 q selected
  have h5 (q : Pattern) (selected : d223520 q = 0) : d224914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223520, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223520, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223521 q = 0) : d224915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223521, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223521, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223522 q = 0) : d224916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223522, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223522, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223524 q = 0) : d224931 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223524, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22074 q selected
    | true =>
      simp only [d223524, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22076 q selected
  have h9 (q : Pattern) (selected : d223525 q = 0) : d224932 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223525, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223525, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223526 q = 0) : d224933 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223526, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223526, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223527 q = 0) : d224934 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223527, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223527, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223528 q = 0) : d224944 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223528, d224944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223528, d224944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223529 q = 0) : d224945 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223529, d224945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223529, d224945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22078 (p : Pattern) (selected : d223533 p = 0) : d224936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223524 q = 0) : d224931 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223524, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22074 q selected
    | true =>
      simp only [d223524, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22076 q selected
  have h2 (q : Pattern) (selected : d223525 q = 0) : d224932 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223525, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223525, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223526 q = 0) : d224933 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223526, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223526, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223527 q = 0) : d224934 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223527, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223527, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223532 q = 0) : d224935 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223532, d224935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223532, d224935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223533 q = 0) : d224936 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223533, d224936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223533, d224936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22079 (p : Pattern) (selected : d223539 p = 0) : d224951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223530 q = 0) : d224946 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223530, d224946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22077 q selected
    | true =>
      simp only [d223530, d224946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223531 q = 0) : d224947 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223531, d224947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223531, d224947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223534 q = 0) : d224937 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223534, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22078 q selected
    | true =>
      simp only [d223534, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223535 q = 0) : d224938 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223535, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223535, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223536 q = 0) : d224948 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223536, d224948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223536, d224948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223537 q = 0) : d224949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223537, d224949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223537, d224949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223538 q = 0) : d224950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223538, d224950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223538, d224950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223539 q = 0) : d224951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223539, d224951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223539, d224951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22080 (p : Pattern) (selected : d223543 p = 0) : d224955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223534 q = 0) : d224937 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223534, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22078 q selected
    | true =>
      simp only [d223534, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223535 q = 0) : d224938 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223535, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223535, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223540 q = 0) : d224952 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223540, d224952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223540, d224952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223541 q = 0) : d224953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223541, d224953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223541, d224953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223542 q = 0) : d224954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223542, d224954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223542, d224954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223543 q = 0) : d224955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223543, d224955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223543, d224955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22081 (p : Pattern) (selected : d223547 p = 0) : d224945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223471 q = 0) : d224909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22063 q selected
    | true =>
      simp only [d223471, d224909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
  have h2 (q : Pattern) (selected : d223472 q = 0) : d224910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223472, d224910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223473 q = 0) : d224911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223473, d224911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223475 q = 0) : d224913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
    | true =>
      simp only [d223475, d224913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22066 q selected
  have h5 (q : Pattern) (selected : d223476 q = 0) : d224914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223476, d224914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223477 q = 0) : d224915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223477, d224915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223478 q = 0) : d224916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223478, d224916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223493 q = 0) : d224931 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223493, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22065 q selected
    | true =>
      simp only [d223493, d224931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22070 q selected
  have h9 (q : Pattern) (selected : d223494 q = 0) : d224932 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223494, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223494, d224932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223495 q = 0) : d224933 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223495, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223495, d224933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223496 q = 0) : d224934 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223496, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223496, d224934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223546 q = 0) : d224944 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223546, d224944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223546, d224944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223547 q = 0) : d224945 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223547, d224945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223547, d224945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22082 (p : Pattern) (selected : d223553 p = 0) : d224961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223548 q = 0) : d224946 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223548, d224946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22081 q selected
    | true =>
      simp only [d223548, d224946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223549 q = 0) : d224947 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223549, d224947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223549, d224947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223550 q = 0) : d224958 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223550, d224958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223550, d224958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223551 q = 0) : d224959 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223551, d224959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223551, d224959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223552 q = 0) : d224960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223552, d224960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223552, d224960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223553 q = 0) : d224961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223553, d224961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223553, d224961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22083 (p : Pattern) (selected : d223559 p = 0) : d224967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223505 q = 0) : d224943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223505, d224943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22069 q selected
    | true =>
      simp only [d223505, d224943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22072 q selected
  have h2 (q : Pattern) (selected : d223544 q = 0) : d224956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223544, d224956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22079 q selected
    | true =>
      simp only [d223544, d224956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22080 q selected
  have h3 (q : Pattern) (selected : d223545 q = 0) : d224957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223545, d224957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223545, d224957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223554 q = 0) : d224962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223554, d224962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22082 q selected
    | true =>
      simp only [d223554, d224962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223555 q = 0) : d224963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223555, d224963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223555, d224963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223556 q = 0) : d224964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223556, d224964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223556, d224964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223557 q = 0) : d224965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223557, d224965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223557, d224965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223558 q = 0) : d224966 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223558, d224966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223558, d224966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223559 q = 0) : d224967 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223559, d224967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223559, d224967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22084 (p : Pattern) (selected : d223564 p = 0) : d224955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223499 q = 0) : d224937 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223499, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22071 q selected
    | true =>
      simp only [d223499, d224937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223500 q = 0) : d224938 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223500, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223500, d224938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223561 q = 0) : d224952 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223561, d224952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223561, d224952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223562 q = 0) : d224953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223562, d224953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223562, d224953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223563 q = 0) : d224954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223563, d224954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223563, d224954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223564 q = 0) : d224955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223564, d224955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223564, d224955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22085 (p : Pattern) (selected : d223570 p = 0) : d224974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223565 q = 0) : d224969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223565, d224969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22084 q selected
    | true =>
      simp only [d223565, d224969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223566 q = 0) : d224970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223566, d224970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223566, d224970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223567 q = 0) : d224971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223567, d224971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223567, d224971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223568 q = 0) : d224972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223568, d224972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223568, d224972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223569 q = 0) : d224973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223569, d224973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223569, d224973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223570 q = 0) : d224974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223570, d224974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223570, d224974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22086 (p : Pattern) (selected : d223576 p = 0) : d224980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223289 q = 0) : d224769 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223289, d224769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223289, d224769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22023 q selected
  have h2 (q : Pattern) (selected : d223290 q = 0) : d224770 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223290, d224770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223290, d224770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223299 q = 0) : d224779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223299, d224779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22023 q selected
    | true =>
      simp only [d223299, d224779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22026 q selected
  have h4 (q : Pattern) (selected : d223300 q = 0) : d224780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223300, d224780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223300, d224780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223301 q = 0) : d224781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223301, d224781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223301, d224781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223423 q = 0) : d224861 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223423, d224861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22047 q selected
    | true =>
      simp only [d223423, d224861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22057 q selected
  have h7 (q : Pattern) (selected : d223441 q = 0) : d224879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223441, d224879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22058 q selected
    | true =>
      simp only [d223441, d224879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22059 q selected
  have h8 (q : Pattern) (selected : d223442 q = 0) : d224880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223442, d224880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223442, d224880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223443 q = 0) : d224881 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223443, d224881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223443, d224881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223444 q = 0) : d224882 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223444, d224882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223444, d224882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223448 q = 0) : d224886 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223448, d224886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223448, d224886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22060 q selected
  have h12 (q : Pattern) (selected : d223450 q = 0) : d224888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223450, d224888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223450, d224888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22061 q selected
  have h13 (q : Pattern) (selected : d223451 q = 0) : d224889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223451, d224889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223451, d224889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223452 q = 0) : d224890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223452, d224890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223452, d224890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223453 q = 0) : d224891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223453, d224891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d223453, d224891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d223454 q = 0) : d224892 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223454, d224892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223454, d224892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223560 q = 0) : d224968 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223560, d224968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223560, d224968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22083 q selected
  have h18 (q : Pattern) (selected : d223571 q = 0) : d224975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223571, d224975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223571, d224975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22085 q selected
  have h19 (q : Pattern) (selected : d223572 q = 0) : d224976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223572, d224976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223572, d224976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223573 q = 0) : d224977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223573, d224977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223573, d224977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d223574 q = 0) : d224978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223574, d224978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d223574, d224978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d223575 q = 0) : d224979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223575, d224979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223575, d224979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223576 q = 0) : d224980 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223576, d224980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223576, d224980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22087 (p : Pattern) (selected : d223582 p = 0) : d224986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223577 q = 0) : d224981 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223577, d224981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223577, d224981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22086 q selected
  have h2 (q : Pattern) (selected : d223578 q = 0) : d224982 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223578, d224982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223578, d224982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223579 q = 0) : d224983 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223579, d224983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223579, d224983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223580 q = 0) : d224984 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223580, d224984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223580, d224984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223581 q = 0) : d224985 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223581, d224985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223581, d224985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223582 q = 0) : d224986 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223582, d224986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223582, d224986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22088 (p : Pattern) (selected : d223589 p = 0) : d224993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118189 q = 0) : d119734 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118190 q = 0) : d119735 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223587 q = 0) : d224991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223587, d224991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223587, d224991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118206 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118207 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223588 q = 0) : d224992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223588, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223588, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223589 q = 0) : d224993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223589, d224993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223589, d224993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22089 (p : Pattern) (selected : d223591 p = 0) : d224995 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118193 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118194 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118206 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118207 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223590 q = 0) : d224994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223590, d224994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223590, d224994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118208 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223591 q = 0) : d224995 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223591, d224995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223591, d224995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22090 (p : Pattern) (selected : d223595 p = 0) : d224999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118206 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118207 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118208 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223595 q = 0) : d224999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223595, d224999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223595, d224999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22091 (p : Pattern) (selected : d223600 p = 0) : d225004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118198 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118199 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118213 q = 0) : d119758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118213, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118213, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223600 q = 0) : d225004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223600, d225004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223600, d225004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22092 (p : Pattern) (selected : d223606 p = 0) : d225010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223592 q = 0) : d224996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22088 q selected
    | true =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
  have h2 (q : Pattern) (selected : d223593 q = 0) : d224997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223594 q = 0) : d224998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223596 q = 0) : d225000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
    | true =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22090 q selected
  have h5 (q : Pattern) (selected : d223597 q = 0) : d225001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223598 q = 0) : d225002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223599 q = 0) : d225003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223601 q = 0) : d225005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223601, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
    | true =>
      simp only [d223601, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22091 q selected
  have h9 (q : Pattern) (selected : d223602 q = 0) : d225006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223602, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223602, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223603 q = 0) : d225007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223603, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223603, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223604 q = 0) : d225008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223604, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223604, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223605 q = 0) : d225009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223605, d225009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223605, d225009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223606 q = 0) : d225010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223606, d225010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223606, d225010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22093 (p : Pattern) (selected : d223610 p = 0) : d225014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223601 q = 0) : d225005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223601, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
    | true =>
      simp only [d223601, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22091 q selected
  have h2 (q : Pattern) (selected : d223602 q = 0) : d225006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223602, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223602, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223603 q = 0) : d225007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223603, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223603, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223604 q = 0) : d225008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223604, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223604, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223609 q = 0) : d225013 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223609, d225013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223609, d225013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223610 q = 0) : d225014 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223610, d225014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223610, d225014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22094 (p : Pattern) (selected : d223616 p = 0) : d225020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223614 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223615 q = 0) : d225019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223615, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223615, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223616 q = 0) : d225020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223616, d225020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223616, d225020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22095 (p : Pattern) (selected : d223620 p = 0) : d225024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223618 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223619 q = 0) : d225023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223619, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223619, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223620 q = 0) : d225024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223620, d225024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223620, d225024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22096 (p : Pattern) (selected : d223626 p = 0) : d225030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223621 q = 0) : d225025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223621, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22094 q selected
    | true =>
      simp only [d223621, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22095 q selected
  have h2 (q : Pattern) (selected : d223622 q = 0) : d225026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223622, d225026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223622, d225026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223623 q = 0) : d225027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223623, d225027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223623, d225027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223624 q = 0) : d225028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223624, d225028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223624, d225028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223625 q = 0) : d225029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223625, d225029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223625, d225029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223626 q = 0) : d225030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223626, d225030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223626, d225030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22097 (p : Pattern) (selected : d223629 p = 0) : d225033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223614 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223615 q = 0) : d225019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223615, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223615, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223629 q = 0) : d225033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223629, d225033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223629, d225033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22098 (p : Pattern) (selected : d223630 p = 0) : d225034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223618 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223619 q = 0) : d225023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223619, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223619, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223630 q = 0) : d225034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223630, d225034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223630, d225034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22099 (p : Pattern) (selected : d223636 p = 0) : d225040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223621 q = 0) : d225025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223621, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22094 q selected
    | true =>
      simp only [d223621, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22095 q selected
  have h2 (q : Pattern) (selected : d223622 q = 0) : d225026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223622, d225026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223622, d225026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223623 q = 0) : d225027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223623, d225027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223623, d225027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223624 q = 0) : d225028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223624, d225028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223624, d225028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223625 q = 0) : d225029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223625, d225029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223625, d225029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223631 q = 0) : d225035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223631, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22097 q selected
    | true =>
      simp only [d223631, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22098 q selected
  have h7 (q : Pattern) (selected : d223632 q = 0) : d225036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223632, d225036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223632, d225036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223633 q = 0) : d225037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223633, d225037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223633, d225037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223634 q = 0) : d225038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223634, d225038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223634, d225038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223635 q = 0) : d225039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223635, d225039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223635, d225039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223636 q = 0) : d225040 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223636, d225040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223636, d225040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22100 (p : Pattern) (selected : d223641 p = 0) : d225045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223614 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223640 q = 0) : d225044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223640, d225044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223640, d225044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223641 q = 0) : d225045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223641, d225045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223641, d225045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22101 (p : Pattern) (selected : d223643 p = 0) : d225047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223618 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223642 q = 0) : d225046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223642, d225046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223642, d225046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223643 q = 0) : d225047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223643, d225047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223643, d225047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22102 (p : Pattern) (selected : d223650 p = 0) : d225054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223648 q = 0) : d225052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223648, d225052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223648, d225052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223649 q = 0) : d225053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223649, d225053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223649, d225053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223650 q = 0) : d225054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223650, d225054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223650, d225054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22103 (p : Pattern) (selected : d223653 p = 0) : d225057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223651 q = 0) : d225055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223651, d225055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223651, d225055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223652 q = 0) : d225056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223652, d225056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223652, d225056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223653 q = 0) : d225057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223653, d225057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223653, d225057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22104 (p : Pattern) (selected : d223658 p = 0) : d225062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118270 q = 0) : d119815 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
    | true =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118271 q = 0) : d119816 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118272 q = 0) : d119817 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118272, d119817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118272, d119817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118273 q = 0) : d119818 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118273, d119818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118273, d119818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223657 q = 0) : d225061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223657, d225061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223657, d225061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223658 q = 0) : d225062 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223658, d225062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223658, d225062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22105 (p : Pattern) (selected : d223662 p = 0) : d225066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118206 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118207 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223588 q = 0) : d224992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223588, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223588, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118208 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223662 q = 0) : d225066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223662, d225066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223662, d225066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22106 (p : Pattern) (selected : d223668 p = 0) : d225072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223659 q = 0) : d225063 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223659, d225063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22104 q selected
    | true =>
      simp only [d223659, d225063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22088 q selected
  have h2 (q : Pattern) (selected : d223660 q = 0) : d225064 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223660, d225064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223660, d225064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223661 q = 0) : d225065 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223661, d225065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223661, d225065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223663 q = 0) : d225067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223663, d225067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22088 q selected
    | true =>
      simp only [d223663, d225067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22105 q selected
  have h5 (q : Pattern) (selected : d223664 q = 0) : d225068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223664, d225068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223664, d225068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223665 q = 0) : d225069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223665, d225069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223665, d225069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223666 q = 0) : d225070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223666, d225070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223666, d225070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223592 q = 0) : d224996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22088 q selected
    | true =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
  have h9 (q : Pattern) (selected : d223593 q = 0) : d224997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223594 q = 0) : d224998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223596 q = 0) : d225000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
    | true =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22090 q selected
  have h12 (q : Pattern) (selected : d223597 q = 0) : d225001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223598 q = 0) : d225002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223599 q = 0) : d225003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223667 q = 0) : d225071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223667, d225071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223667, d225071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223668 q = 0) : d225072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223668, d225072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223668, d225072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro22107 (p : Pattern) (selected : d223673 p = 0) : d225077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223592 q = 0) : d224996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22088 q selected
    | true =>
      simp only [d223592, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
  have h2 (q : Pattern) (selected : d223593 q = 0) : d224997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223593, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223594 q = 0) : d224998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223594, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223596 q = 0) : d225000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22089 q selected
    | true =>
      simp only [d223596, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22090 q selected
  have h5 (q : Pattern) (selected : d223597 q = 0) : d225001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223597, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223598 q = 0) : d225002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223598, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223599 q = 0) : d225003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223599, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223671 q = 0) : d225075 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223671, d225075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223671, d225075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223672 q = 0) : d225076 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223672, d225076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223672, d225076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223673 q = 0) : d225077 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223673, d225077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223673, d225077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22108 (p : Pattern) (selected : d223679 p = 0) : d225083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223669 q = 0) : d225073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223669, d225073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22106 q selected
    | true =>
      simp only [d223669, d225073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223670 q = 0) : d225074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223670, d225074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223670, d225074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223674 q = 0) : d225078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22107 q selected
    | true =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223675 q = 0) : d225079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223676 q = 0) : d225080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223676, d225080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223676, d225080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223677 q = 0) : d225081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223677, d225081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223677, d225081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223678 q = 0) : d225082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223678, d225082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223678, d225082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223679 q = 0) : d225083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223679, d225083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223679, d225083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22109 (p : Pattern) (selected : d223683 p = 0) : d225087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223674 q = 0) : d225078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22107 q selected
    | true =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223675 q = 0) : d225079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223680 q = 0) : d225084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223680, d225084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223680, d225084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223681 q = 0) : d225085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223681, d225085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223681, d225085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223682 q = 0) : d225086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223682, d225086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223682, d225086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223683 q = 0) : d225087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223683, d225087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223683, d225087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22110 (p : Pattern) (selected : d223687 p = 0) : d224993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118300 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
    | true =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118301 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118302 q = 0) : d119734 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118302, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118302, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118303 q = 0) : d119735 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118303, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118303, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223685 q = 0) : d224991 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223685, d224991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223685, d224991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118319 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118320 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223686 q = 0) : d224992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223686, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223686, d224992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223687 q = 0) : d224993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223687, d224993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223687, d224993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22111 (p : Pattern) (selected : d223689 p = 0) : d224995 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118306 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118307 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118319 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118320 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223688 q = 0) : d224994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223688, d224994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223688, d224994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118321 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223689 q = 0) : d224995 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223689, d224995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223689, d224995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22112 (p : Pattern) (selected : d223693 p = 0) : d224999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118319 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118320 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118321 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223693 q = 0) : d224999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223693, d224999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223693, d224999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22113 (p : Pattern) (selected : d223698 p = 0) : d225004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118311 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118312 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118326 q = 0) : d119758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118326, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118326, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223698 q = 0) : d225004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223698, d225004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223698, d225004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22114 (p : Pattern) (selected : d223704 p = 0) : d225010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223690 q = 0) : d224996 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223690, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22110 q selected
    | true =>
      simp only [d223690, d224996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22111 q selected
  have h2 (q : Pattern) (selected : d223691 q = 0) : d224997 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223691, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223691, d224997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223692 q = 0) : d224998 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223692, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223692, d224998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223694 q = 0) : d225000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223694, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22111 q selected
    | true =>
      simp only [d223694, d225000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22112 q selected
  have h5 (q : Pattern) (selected : d223695 q = 0) : d225001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223695, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223695, d225001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223696 q = 0) : d225002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223696, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223696, d225002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223697 q = 0) : d225003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223697, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223697, d225003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223699 q = 0) : d225005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223699, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22111 q selected
    | true =>
      simp only [d223699, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22113 q selected
  have h9 (q : Pattern) (selected : d223700 q = 0) : d225006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223700, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223700, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223701 q = 0) : d225007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223701, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223701, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223702 q = 0) : d225008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223702, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223702, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223703 q = 0) : d225009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223703, d225009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223703, d225009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223704 q = 0) : d225010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223704, d225010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223704, d225010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22115 (p : Pattern) (selected : d223708 p = 0) : d225014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223699 q = 0) : d225005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223699, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22111 q selected
    | true =>
      simp only [d223699, d225005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22113 q selected
  have h2 (q : Pattern) (selected : d223700 q = 0) : d225006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223700, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223700, d225006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223701 q = 0) : d225007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223701, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223701, d225007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223702 q = 0) : d225008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223702, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223702, d225008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223707 q = 0) : d225013 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223707, d225013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223707, d225013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223708 q = 0) : d225014 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223708, d225014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223708, d225014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22116 (p : Pattern) (selected : d223714 p = 0) : d225020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223705 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223705, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22114 q selected
    | true =>
      simp only [d223705, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223706 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223706, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223706, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223709 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22115 q selected
    | true =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223710 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223711 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223711, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223711, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223712 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223712, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223712, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223713 q = 0) : d225019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223713, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223713, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223714 q = 0) : d225020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223714, d225020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223714, d225020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22117 (p : Pattern) (selected : d223718 p = 0) : d225024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223709 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22115 q selected
    | true =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223710 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223715 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223715, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223715, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223716 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223716, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223716, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223717 q = 0) : d225023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223717, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223717, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223718 q = 0) : d225024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223718, d225024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223718, d225024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22118 (p : Pattern) (selected : d223724 p = 0) : d225093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223721 q = 0) : d225090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223721, d225090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223721, d225090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223722 q = 0) : d225091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223722, d225091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223722, d225091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223723 q = 0) : d225092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223723, d225092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223723, d225092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223724 q = 0) : d225093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223724, d225093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223724, d225093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22119 (p : Pattern) (selected : d223730 p = 0) : d225099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223644 q = 0) : d225048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223644, d225048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22100 q selected
    | true =>
      simp only [d223644, d225048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22101 q selected
  have h2 (q : Pattern) (selected : d223645 q = 0) : d225049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223645, d225049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223645, d225049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223646 q = 0) : d225050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223646, d225050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223646, d225050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223647 q = 0) : d225051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223647, d225051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223647, d225051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223654 q = 0) : d225058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223654, d225058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22102 q selected
    | true =>
      simp only [d223654, d225058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22103 q selected
  have h6 (q : Pattern) (selected : d223655 q = 0) : d225059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223655, d225059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223655, d225059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223656 q = 0) : d225060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223656, d225060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223656, d225060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223684 q = 0) : d225088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223684, d225088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22108 q selected
    | true =>
      simp only [d223684, d225088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22109 q selected
  have h9 (q : Pattern) (selected : d223719 q = 0) : d225025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223719, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22116 q selected
    | true =>
      simp only [d223719, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22117 q selected
  have h10 (q : Pattern) (selected : d223720 q = 0) : d225089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223720, d225089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223720, d225089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223725 q = 0) : d225094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223725, d225094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22118 q selected
    | true =>
      simp only [d223725, d225094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223726 q = 0) : d225095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223726, d225095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223726, d225095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223727 q = 0) : d225096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223727, d225096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223727, d225096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223728 q = 0) : d225097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223728, d225097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223728, d225097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223729 q = 0) : d225098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223729, d225098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223729, d225098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223730 q = 0) : d225099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223730, d225099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223730, d225099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22120 (p : Pattern) (selected : d223731 p = 0) : d225100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223614 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223614, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223640 q = 0) : d225044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223640, d225044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223640, d225044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223731 q = 0) : d225100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223731, d225100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223731, d225100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22121 (p : Pattern) (selected : d223732 p = 0) : d225101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223618 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223618, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223642 q = 0) : d225046 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223642, d225046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223642, d225046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223732 q = 0) : d225101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223732, d225101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223732, d225101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22122 (p : Pattern) (selected : d223737 p = 0) : d225106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223613 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223613, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223648 q = 0) : d225052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223648, d225052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223648, d225052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223649 q = 0) : d225053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223649, d225053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223649, d225053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223737 q = 0) : d225106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223737, d225106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223737, d225106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22123 (p : Pattern) (selected : d223738 p = 0) : d225107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223617 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223617, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223651 q = 0) : d225055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223651, d225055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223651, d225055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223652 q = 0) : d225056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223652, d225056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223652, d225056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223738 q = 0) : d225107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223738, d225107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223738, d225107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22124 (p : Pattern) (selected : d223742 p = 0) : d225111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223669 q = 0) : d225073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223669, d225073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22106 q selected
    | true =>
      simp only [d223669, d225073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223670 q = 0) : d225074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223670, d225074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223670, d225074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223674 q = 0) : d225078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22107 q selected
    | true =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223675 q = 0) : d225079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223676 q = 0) : d225080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223676, d225080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223676, d225080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223677 q = 0) : d225081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223677, d225081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223677, d225081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223678 q = 0) : d225082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223678, d225082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223678, d225082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223742 q = 0) : d225111 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223742, d225111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223742, d225111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22125 (p : Pattern) (selected : d223743 p = 0) : d225112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223674 q = 0) : d225078 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22107 q selected
    | true =>
      simp only [d223674, d225078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223675 q = 0) : d225079 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223675, d225079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223611 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22093 q selected
    | true =>
      simp only [d223611, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223612 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223612, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223680 q = 0) : d225084 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223680, d225084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223680, d225084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223681 q = 0) : d225085 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223681, d225085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223681, d225085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223682 q = 0) : d225086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223682, d225086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223682, d225086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223743 q = 0) : d225112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223743, d225112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223743, d225112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22126 (p : Pattern) (selected : d223745 p = 0) : d225033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223705 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223705, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22114 q selected
    | true =>
      simp only [d223705, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223706 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223706, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223706, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223709 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22115 q selected
    | true =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223710 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223711 q = 0) : d225017 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223711, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223711, d225017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223712 q = 0) : d225018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223712, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223712, d225018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223713 q = 0) : d225019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223713, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223713, d225019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223745 q = 0) : d225033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223745, d225033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223745, d225033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22127 (p : Pattern) (selected : d223746 p = 0) : d225034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223709 q = 0) : d225015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22115 q selected
    | true =>
      simp only [d223709, d225015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223710 q = 0) : d225016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223710, d225016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223715 q = 0) : d225021 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223715, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223715, d225021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223716 q = 0) : d225022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223716, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223716, d225022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223717 q = 0) : d225023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223717, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223717, d225023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223746 q = 0) : d225034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223746, d225034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223746, d225034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22128 (p : Pattern) (selected : d223749 p = 0) : d225115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223607 q = 0) : d225011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22092 q selected
    | true =>
      simp only [d223607, d225011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223608 q = 0) : d225012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223608, d225012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223721 q = 0) : d225090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223721, d225090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223721, d225090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223722 q = 0) : d225091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223722, d225091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223722, d225091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223723 q = 0) : d225092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223723, d225092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223723, d225092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223749 q = 0) : d225115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223749, d225115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223749, d225115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22129 (p : Pattern) (selected : d223755 p = 0) : d225121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223644 q = 0) : d225048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223644, d225048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22100 q selected
    | true =>
      simp only [d223644, d225048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22101 q selected
  have h2 (q : Pattern) (selected : d223645 q = 0) : d225049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223645, d225049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223645, d225049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223646 q = 0) : d225050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223646, d225050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223646, d225050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223647 q = 0) : d225051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223647, d225051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223647, d225051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223654 q = 0) : d225058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223654, d225058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22102 q selected
    | true =>
      simp only [d223654, d225058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22103 q selected
  have h6 (q : Pattern) (selected : d223655 q = 0) : d225059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223655, d225059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223655, d225059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223656 q = 0) : d225060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223656, d225060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223656, d225060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223684 q = 0) : d225088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223684, d225088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22108 q selected
    | true =>
      simp only [d223684, d225088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22109 q selected
  have h9 (q : Pattern) (selected : d223719 q = 0) : d225025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223719, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22116 q selected
    | true =>
      simp only [d223719, d225025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22117 q selected
  have h10 (q : Pattern) (selected : d223720 q = 0) : d225089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223720, d225089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223720, d225089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223725 q = 0) : d225094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223725, d225094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22118 q selected
    | true =>
      simp only [d223725, d225094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223726 q = 0) : d225095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223726, d225095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223726, d225095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223727 q = 0) : d225096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223727, d225096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223727, d225096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223728 q = 0) : d225097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223728, d225097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223728, d225097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223729 q = 0) : d225098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223729, d225098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223729, d225098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223733 q = 0) : d225102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223733, d225102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22120 q selected
    | true =>
      simp only [d223733, d225102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22121 q selected
  have h17 (q : Pattern) (selected : d223734 q = 0) : d225103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223734, d225103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223734, d225103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223735 q = 0) : d225104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223735, d225104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223735, d225104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d223736 q = 0) : d225105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223736, d225105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223736, d225105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223739 q = 0) : d225108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223739, d225108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22122 q selected
    | true =>
      simp only [d223739, d225108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22123 q selected
  have h21 (q : Pattern) (selected : d223740 q = 0) : d225109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223740, d225109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223740, d225109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d223741 q = 0) : d225110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223741, d225110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223741, d225110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223744 q = 0) : d225113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223744, d225113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22124 q selected
    | true =>
      simp only [d223744, d225113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22125 q selected
  have h24 (q : Pattern) (selected : d223747 q = 0) : d225035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223747, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22126 q selected
    | true =>
      simp only [d223747, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22127 q selected
  have h25 (q : Pattern) (selected : d223748 q = 0) : d225114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223748, d225114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d223748, d225114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d223750 q = 0) : d225116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223750, d225116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22128 q selected
    | true =>
      simp only [d223750, d225116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d223751 q = 0) : d225117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223751, d225117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d223751, d225117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d223752 q = 0) : d225118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223752, d225118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d223752, d225118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d223753 q = 0) : d225119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223753, d225119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d223753, d225119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d223754 q = 0) : d225120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223754, d225120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223754, d225120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d223755 q = 0) : d225121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223755, d225121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223755, d225121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22130 (p : Pattern) (selected : d223767 p = 0) : d225133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223757 q = 0) : d225123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223757, d225123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22109 q selected
    | true =>
      simp only [d223757, d225123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22095 q selected
  have h2 (q : Pattern) (selected : d223758 q = 0) : d225124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223758, d225124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223758, d225124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223759 q = 0) : d225125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223759, d225125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223759, d225125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223760 q = 0) : d225126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223760, d225126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223760, d225126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223761 q = 0) : d225127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223761, d225127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223761, d225127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223762 q = 0) : d225128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223762, d225128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22095 q selected
    | true =>
      simp only [d223762, d225128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223763 q = 0) : d225129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223763, d225129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223763, d225129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223764 q = 0) : d225130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223764, d225130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223764, d225130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223765 q = 0) : d225131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223765, d225131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223765, d225131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223766 q = 0) : d225132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223766, d225132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223766, d225132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223767 q = 0) : d225133 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223767, d225133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223767, d225133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22131 (p : Pattern) (selected : d223773 p = 0) : d225139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223762 q = 0) : d225128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223762, d225128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22095 q selected
    | true =>
      simp only [d223762, d225128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223763 q = 0) : d225129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223763, d225129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223763, d225129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223764 q = 0) : d225130 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223764, d225130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223764, d225130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223765 q = 0) : d225131 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223765, d225131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223765, d225131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223766 q = 0) : d225132 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223766, d225132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223766, d225132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223768 q = 0) : d225134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223768, d225134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22098 q selected
    | true =>
      simp only [d223768, d225134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223769 q = 0) : d225135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223769, d225135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223769, d225135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223770 q = 0) : d225136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223770, d225136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223770, d225136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223771 q = 0) : d225137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223771, d225137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223771, d225137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223772 q = 0) : d225138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223772, d225138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223772, d225138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223773 q = 0) : d225139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223773, d225139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223773, d225139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22132 (p : Pattern) (selected : d223780 p = 0) : d225146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223744 q = 0) : d225113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223744, d225113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22124 q selected
    | true =>
      simp only [d223744, d225113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22125 q selected
  have h2 (q : Pattern) (selected : d223747 q = 0) : d225035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223747, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22126 q selected
    | true =>
      simp only [d223747, d225035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22127 q selected
  have h3 (q : Pattern) (selected : d223748 q = 0) : d225114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223748, d225114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223748, d225114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223750 q = 0) : d225116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223750, d225116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22128 q selected
    | true =>
      simp only [d223750, d225116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223751 q = 0) : d225117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223751, d225117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223751, d225117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223752 q = 0) : d225118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223752, d225118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223752, d225118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223778 q = 0) : d225144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223778, d225144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223778, d225144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223779 q = 0) : d225145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223779, d225145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223779, d225145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223780 q = 0) : d225146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223780, d225146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223780, d225146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22133 (p : Pattern) (selected : d223782 p = 0) : d225148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223768 q = 0) : d225134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223768, d225134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22098 q selected
    | true =>
      simp only [d223768, d225134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223769 q = 0) : d225135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223769, d225135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223769, d225135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223770 q = 0) : d225136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223770, d225136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223770, d225136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223771 q = 0) : d225137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223771, d225137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223771, d225137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223772 q = 0) : d225138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223772, d225138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223772, d225138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223782 q = 0) : d225148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223782, d225148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223782, d225148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22134 (p : Pattern) (selected : d223789 p = 0) : d225155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118416 q = 0) : d119910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118416, d119910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118416, d119910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
  have h2 (q : Pattern) (selected : d118270 q = 0) : d119815 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
    | true =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118417 q = 0) : d119911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118417, d119911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118417, d119911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118271 q = 0) : d119816 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118418 q = 0) : d119912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118418, d119912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118418, d119912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118419 q = 0) : d119913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118419, d119913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118419, d119913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223788 q = 0) : d225154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223788, d225154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223788, d225154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223789 q = 0) : d225155 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223789, d225155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223789, d225155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22135 (p : Pattern) (selected : d223792 p = 0) : d225158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118420 q = 0) : d119914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
  have h2 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118421 q = 0) : d119915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118422 q = 0) : d119916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118423 q = 0) : d119917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223790 q = 0) : d225156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223790, d225156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223790, d225156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118445 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
  have h9 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118446 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118447 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118448 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223791 q = 0) : d225157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223791, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223791, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223792 q = 0) : d225158 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223792, d225158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223792, d225158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22136 (p : Pattern) (selected : d223796 p = 0) : d225162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118445 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
  have h2 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118446 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118447 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118448 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223791 q = 0) : d225157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223791, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223791, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118449 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223796 q = 0) : d225162 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223796, d225162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223796, d225162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22137 (p : Pattern) (selected : d223802 p = 0) : d225168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118425 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
  have h2 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118426 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118427 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118428 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118445 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
  have h8 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118446 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118447 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118448 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223801 q = 0) : d225167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223801, d225167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223801, d225167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118449 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223802 q = 0) : d225168 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223802, d225168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223802, d225168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22138 (p : Pattern) (selected : d223806 p = 0) : d225172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118445 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
  have h2 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118446 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118447 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118448 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118449 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223806 q = 0) : d225172 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223806, d225172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223806, d225172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22139 (p : Pattern) (selected : d223812 p = 0) : d225178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223793 q = 0) : d225159 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223793, d225159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22134 q selected
    | true =>
      simp only [d223793, d225159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22135 q selected
  have h2 (q : Pattern) (selected : d223794 q = 0) : d225160 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223794, d225160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223794, d225160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223795 q = 0) : d225161 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223795, d225161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223795, d225161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223797 q = 0) : d225163 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223797, d225163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22135 q selected
    | true =>
      simp only [d223797, d225163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22136 q selected
  have h5 (q : Pattern) (selected : d223798 q = 0) : d225164 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223798, d225164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223798, d225164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223799 q = 0) : d225165 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223799, d225165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223799, d225165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223800 q = 0) : d225166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223800, d225166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223800, d225166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223803 q = 0) : d225169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22135 q selected
    | true =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
  have h9 (q : Pattern) (selected : d223804 q = 0) : d225170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223805 q = 0) : d225171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223807 q = 0) : d225173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
    | true =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22138 q selected
  have h12 (q : Pattern) (selected : d223808 q = 0) : d225174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223809 q = 0) : d225175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223810 q = 0) : d225176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223811 q = 0) : d225177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223811, d225177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223811, d225177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223812 q = 0) : d225178 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223812, d225178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223812, d225178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro22140 (p : Pattern) (selected : d223817 p = 0) : d225183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223803 q = 0) : d225169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22135 q selected
    | true =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
  have h2 (q : Pattern) (selected : d223804 q = 0) : d225170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223805 q = 0) : d225171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223807 q = 0) : d225173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
    | true =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22138 q selected
  have h5 (q : Pattern) (selected : d223808 q = 0) : d225174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223809 q = 0) : d225175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223810 q = 0) : d225176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223815 q = 0) : d225181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223815, d225181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223815, d225181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223816 q = 0) : d225182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223816, d225182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223816, d225182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223817 q = 0) : d225183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223817, d225183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223817, d225183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22141 (p : Pattern) (selected : d223823 p = 0) : d225189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223813 q = 0) : d225179 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223813, d225179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22139 q selected
    | true =>
      simp only [d223813, d225179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223814 q = 0) : d225180 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223814, d225180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223814, d225180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223818 q = 0) : d225184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223818, d225184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22140 q selected
    | true =>
      simp only [d223818, d225184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223819 q = 0) : d225185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223819, d225185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223819, d225185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223820 q = 0) : d225186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223820, d225186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223820, d225186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223821 q = 0) : d225187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223821, d225187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223821, d225187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223822 q = 0) : d225188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223822, d225188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223822, d225188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223823 q = 0) : d225189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223823, d225189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223823, d225189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22142 (p : Pattern) (selected : d223824 p = 0) : d225190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118437 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
  have h2 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118438 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118439 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118440 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118467 q = 0) : d119961 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118467, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118467, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223824 q = 0) : d225190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223824, d225190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223824, d225190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22143 (p : Pattern) (selected : d223830 p = 0) : d225196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223825 q = 0) : d225191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223825, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
    | true =>
      simp only [d223825, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22142 q selected
  have h2 (q : Pattern) (selected : d223826 q = 0) : d225192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223826, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223826, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223827 q = 0) : d225193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223827, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223827, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223828 q = 0) : d225194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223828, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223828, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223829 q = 0) : d225195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223829, d225195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223829, d225195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223830 q = 0) : d225196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223830, d225196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223830, d225196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22144 (p : Pattern) (selected : d223836 p = 0) : d225202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223818 q = 0) : d225184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223818, d225184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22140 q selected
    | true =>
      simp only [d223818, d225184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223819 q = 0) : d225185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223819, d225185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223819, d225185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223831 q = 0) : d225197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223831, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22143 q selected
    | true =>
      simp only [d223831, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223832 q = 0) : d225198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223832, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223832, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223833 q = 0) : d225199 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223833, d225199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223833, d225199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223834 q = 0) : d225200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223834, d225200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223834, d225200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223835 q = 0) : d225201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223835, d225201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223835, d225201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223836 q = 0) : d225202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223836, d225202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223836, d225202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22145 (p : Pattern) (selected : d223840 p = 0) : d225158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118481 q = 0) : d119914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118481, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118481, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
  have h2 (q : Pattern) (selected : d118300 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
    | true =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118482 q = 0) : d119915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118482, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118482, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118301 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118483 q = 0) : d119916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118483, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118483, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118484 q = 0) : d119917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118484, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118484, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223838 q = 0) : d225156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223838, d225156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223838, d225156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118498 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
  have h9 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118499 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118500 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118501 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223839 q = 0) : d225157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223839, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223839, d225157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223840 q = 0) : d225158 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223840, d225158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223840, d225158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22146 (p : Pattern) (selected : d223842 p = 0) : d225168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118485 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
  have h2 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118486 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118487 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118488 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118498 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
  have h8 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118499 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118500 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118501 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223841 q = 0) : d225167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223841, d225167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223841, d225167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118502 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223842 q = 0) : d225168 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223842, d225168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223842, d225168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22147 (p : Pattern) (selected : d223846 p = 0) : d225172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118498 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
  have h2 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118499 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118500 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118501 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118502 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223846 q = 0) : d225172 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223846, d225172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223846, d225172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22148 (p : Pattern) (selected : d223851 p = 0) : d225190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118490 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
  have h2 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118491 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118492 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118493 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118507 q = 0) : d119961 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118507, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118507, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223851 q = 0) : d225190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223851, d225190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223851, d225190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22149 (p : Pattern) (selected : d223857 p = 0) : d225205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223843 q = 0) : d225169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223843, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22145 q selected
    | true =>
      simp only [d223843, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22146 q selected
  have h2 (q : Pattern) (selected : d223844 q = 0) : d225170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223844, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223844, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223845 q = 0) : d225171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223845, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223845, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223847 q = 0) : d225173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223847, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22146 q selected
    | true =>
      simp only [d223847, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22147 q selected
  have h5 (q : Pattern) (selected : d223848 q = 0) : d225174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223848, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223848, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223849 q = 0) : d225175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223849, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223849, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223850 q = 0) : d225176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223850, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223850, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223852 q = 0) : d225191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223852, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22146 q selected
    | true =>
      simp only [d223852, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22148 q selected
  have h9 (q : Pattern) (selected : d223853 q = 0) : d225192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223853, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223853, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223854 q = 0) : d225193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223854, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223854, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223855 q = 0) : d225194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223855, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223855, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223856 q = 0) : d225204 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223856, d225204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223856, d225204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223857 q = 0) : d225205 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223857, d225205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223857, d225205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22150 (p : Pattern) (selected : d223861 p = 0) : d225196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223852 q = 0) : d225191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223852, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22146 q selected
    | true =>
      simp only [d223852, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22148 q selected
  have h2 (q : Pattern) (selected : d223853 q = 0) : d225192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223853, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223853, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223854 q = 0) : d225193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223854, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223854, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223855 q = 0) : d225194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223855, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223855, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223860 q = 0) : d225195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223860, d225195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223860, d225195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223861 q = 0) : d225196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223861, d225196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223861, d225196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22151 (p : Pattern) (selected : d223867 p = 0) : d225211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223858 q = 0) : d225206 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223858, d225206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22149 q selected
    | true =>
      simp only [d223858, d225206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223859 q = 0) : d225207 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223859, d225207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223859, d225207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223862 q = 0) : d225197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223862, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22150 q selected
    | true =>
      simp only [d223862, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223863 q = 0) : d225198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223863, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223863, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223864 q = 0) : d225208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223864, d225208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223864, d225208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223865 q = 0) : d225209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223865, d225209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223865, d225209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223866 q = 0) : d225210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223866, d225210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223866, d225210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223867 q = 0) : d225211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223867, d225211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223867, d225211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22152 (p : Pattern) (selected : d223871 p = 0) : d225215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223862 q = 0) : d225197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223862, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22150 q selected
    | true =>
      simp only [d223862, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223863 q = 0) : d225198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223863, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223863, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223868 q = 0) : d225212 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223868, d225212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223868, d225212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223869 q = 0) : d225213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223869, d225213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223869, d225213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223870 q = 0) : d225214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223870, d225214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223870, d225214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223871 q = 0) : d225215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223871, d225215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223871, d225215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22153 (p : Pattern) (selected : d223875 p = 0) : d225205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223803 q = 0) : d225169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22135 q selected
    | true =>
      simp only [d223803, d225169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
  have h2 (q : Pattern) (selected : d223804 q = 0) : d225170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223804, d225170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223805 q = 0) : d225171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223805, d225171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223807 q = 0) : d225173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
    | true =>
      simp only [d223807, d225173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22138 q selected
  have h5 (q : Pattern) (selected : d223808 q = 0) : d225174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223808, d225174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223809 q = 0) : d225175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223809, d225175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223810 q = 0) : d225176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223810, d225176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223825 q = 0) : d225191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223825, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22137 q selected
    | true =>
      simp only [d223825, d225191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22142 q selected
  have h9 (q : Pattern) (selected : d223826 q = 0) : d225192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223826, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223826, d225192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223827 q = 0) : d225193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223827, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223827, d225193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223828 q = 0) : d225194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223828, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223828, d225194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223874 q = 0) : d225204 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223874, d225204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223874, d225204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223875 q = 0) : d225205 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223875, d225205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223875, d225205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22154 (p : Pattern) (selected : d223881 p = 0) : d225221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223876 q = 0) : d225206 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223876, d225206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22153 q selected
    | true =>
      simp only [d223876, d225206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223877 q = 0) : d225207 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223877, d225207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223877, d225207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223878 q = 0) : d225218 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223878, d225218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223878, d225218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223879 q = 0) : d225219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223879, d225219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223879, d225219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223880 q = 0) : d225220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223880, d225220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223880, d225220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223881 q = 0) : d225221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223881, d225221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223881, d225221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22155 (p : Pattern) (selected : d223887 p = 0) : d225227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223837 q = 0) : d225203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223837, d225203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22141 q selected
    | true =>
      simp only [d223837, d225203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22144 q selected
  have h2 (q : Pattern) (selected : d223872 q = 0) : d225216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223872, d225216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22151 q selected
    | true =>
      simp only [d223872, d225216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22152 q selected
  have h3 (q : Pattern) (selected : d223873 q = 0) : d225217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223873, d225217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223873, d225217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223882 q = 0) : d225222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223882, d225222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22154 q selected
    | true =>
      simp only [d223882, d225222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223883 q = 0) : d225223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223883, d225223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223883, d225223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223884 q = 0) : d225224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223884, d225224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223884, d225224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223885 q = 0) : d225225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223885, d225225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223885, d225225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223886 q = 0) : d225226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223886, d225226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223886, d225226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223887 q = 0) : d225227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223887, d225227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223887, d225227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22156 (p : Pattern) (selected : d223892 p = 0) : d225215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223831 q = 0) : d225197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223831, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22143 q selected
    | true =>
      simp only [d223831, d225197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223832 q = 0) : d225198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223832, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223832, d225198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223889 q = 0) : d225212 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223889, d225212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223889, d225212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223890 q = 0) : d225213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223890, d225213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223890, d225213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223891 q = 0) : d225214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223891, d225214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223891, d225214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223892 q = 0) : d225215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223892, d225215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223892, d225215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22157 (p : Pattern) (selected : d223898 p = 0) : d225234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223893 q = 0) : d225229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223893, d225229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22156 q selected
    | true =>
      simp only [d223893, d225229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223894 q = 0) : d225230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223894, d225230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223894, d225230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223895 q = 0) : d225231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223895, d225231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223895, d225231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223896 q = 0) : d225232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223896, d225232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223896, d225232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223897 q = 0) : d225233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223897, d225233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223897, d225233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223898 q = 0) : d225234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223898, d225234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223898, d225234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22158 (p : Pattern) (selected : d223904 p = 0) : d225240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223627 q = 0) : d225031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223627, d225031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223627, d225031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22096 q selected
  have h2 (q : Pattern) (selected : d223628 q = 0) : d225032 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223628, d225032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223628, d225032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223637 q = 0) : d225041 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223637, d225041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22096 q selected
    | true =>
      simp only [d223637, d225041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22099 q selected
  have h4 (q : Pattern) (selected : d223638 q = 0) : d225042 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223638, d225042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223638, d225042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223639 q = 0) : d225043 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223639, d225043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223639, d225043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223756 q = 0) : d225122 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223756, d225122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22119 q selected
    | true =>
      simp only [d223756, d225122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22129 q selected
  have h7 (q : Pattern) (selected : d223774 q = 0) : d225140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223774, d225140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22130 q selected
    | true =>
      simp only [d223774, d225140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22131 q selected
  have h8 (q : Pattern) (selected : d223775 q = 0) : d225141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223775, d225141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223775, d225141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223776 q = 0) : d225142 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223776, d225142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223776, d225142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d223777 q = 0) : d225143 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223777, d225143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223777, d225143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223781 q = 0) : d225147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223781, d225147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223781, d225147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22132 q selected
  have h12 (q : Pattern) (selected : d223783 q = 0) : d225149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223783, d225149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223783, d225149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22133 q selected
  have h13 (q : Pattern) (selected : d223784 q = 0) : d225150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223784, d225150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223784, d225150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223785 q = 0) : d225151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223785, d225151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223785, d225151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223786 q = 0) : d225152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223786, d225152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d223786, d225152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d223787 q = 0) : d225153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223787, d225153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223787, d225153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223888 q = 0) : d225228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223888, d225228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223888, d225228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22155 q selected
  have h18 (q : Pattern) (selected : d223899 q = 0) : d225235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223899, d225235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223899, d225235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22157 q selected
  have h19 (q : Pattern) (selected : d223900 q = 0) : d225236 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223900, d225236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223900, d225236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d223901 q = 0) : d225237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223901, d225237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d223901, d225237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d223902 q = 0) : d225238 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223902, d225238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d223902, d225238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d223903 q = 0) : d225239 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223903, d225239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d223903, d225239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d223904 q = 0) : d225240 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223904, d225240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223904, d225240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22159 (p : Pattern) (selected : d223910 p = 0) : d225246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223905 q = 0) : d225241 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223905, d225241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223905, d225241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22158 q selected
  have h2 (q : Pattern) (selected : d223906 q = 0) : d225242 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223906, d225242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223906, d225242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223907 q = 0) : d225243 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223907, d225243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223907, d225243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223908 q = 0) : d225244 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223908, d225244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223908, d225244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223909 q = 0) : d225245 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223909, d225245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223909, d225245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223910 q = 0) : d225246 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223910, d225246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223910, d225246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22160 (p : Pattern) (selected : d223916 p = 0) : d225252 p = 1 := by
  have h0 (q : Pattern) (selected : d222647 q = 0) : d224265 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d222647, d224265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21854 q selected
    | true =>
      simp only [d222647, d224265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21886 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d222942 q = 0) : d224492 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d222942, d224492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222942, d224492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21948 q selected
  have h3 (q : Pattern) (selected : d222943 q = 0) : d224493 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d222943, d224493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222943, d224493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223246 q = 0) : d224726 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223246, d224726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223246, d224726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22014 q selected
  have h5 (q : Pattern) (selected : d223247 q = 0) : d224727 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223247, d224727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223247, d224727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223248 q = 0) : d224728 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223248, d224728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223248, d224728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223583 q = 0) : d224987 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223583, d224987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223583, d224987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22087 q selected
  have h8 (q : Pattern) (selected : d223584 q = 0) : d224988 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223584, d224988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223584, d224988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223585 q = 0) : d224989 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223585, d224989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223585, d224989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223586 q = 0) : d224990 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d223586, d224990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223586, d224990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223911 q = 0) : d225247 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d223911, d225247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223911, d225247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22159 q selected
  have h12 (q : Pattern) (selected : d223912 q = 0) : d225248 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d223912, d225248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223912, d225248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223913 q = 0) : d225249 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d223913, d225249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223913, d225249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223914 q = 0) : d225250 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d223914, d225250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223914, d225250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223915 q = 0) : d225251 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d223915, d225251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223915, d225251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223916 q = 0) : d225252 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d223916, d225252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223916, d225252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22161 (p : Pattern) (selected : d223922 p = 0) : d225258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223917 q = 0) : d225253 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d223917, d225253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22160 q selected
    | true =>
      simp only [d223917, d225253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223918 q = 0) : d225254 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d223918, d225254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223918, d225254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223919 q = 0) : d225255 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d223919, d225255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223919, d225255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223920 q = 0) : d225256 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d223920, d225256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223920, d225256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223921 q = 0) : d225257 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d223921, d225257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223921, d225257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223922 q = 0) : d225258 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d223922, d225258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223922, d225258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22162 (p : Pattern) (selected : d223928 p = 0) : d225264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223923 q = 0) : d225259 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d223923, d225259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22161 q selected
    | true =>
      simp only [d223923, d225259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223924 q = 0) : d225260 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d223924, d225260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223924, d225260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223925 q = 0) : d225261 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d223925, d225261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223925, d225261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223926 q = 0) : d225262 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d223926, d225262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223926, d225262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223927 q = 0) : d225263 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d223927, d225263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223927, d225263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223928 q = 0) : d225264 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d223928, d225264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223928, d225264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22163 (p : Pattern) (selected : d223933 p = 0) : d225269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223929 q = 0) : d225265 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d223929, d225265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22162 q selected
    | true =>
      simp only [d223929, d225265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223930 q = 0) : d225266 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d223930, d225266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223930, d225266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223931 q = 0) : d225267 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d223931, d225267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223931, d225267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223932 q = 0) : d225268 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d223932, d225268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223932, d225268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223933 q = 0) : d225269 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d223933, d225269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223933, d225269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22164 (p : Pattern) (selected : d223939 p = 0) : d225275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223934 q = 0) : d225270 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d223934, d225270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22163 q selected
    | true =>
      simp only [d223934, d225270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223935 q = 0) : d225271 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d223935, d225271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223935, d225271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223936 q = 0) : d225272 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d223936, d225272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223936, d225272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223937 q = 0) : d225273 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d223937, d225273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223937, d225273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223938 q = 0) : d225274 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d223938, d225274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223938, d225274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223939 q = 0) : d225275 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d223939, d225275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223939, d225275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22165 (p : Pattern) (selected : d223945 p = 0) : d225281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223940 q = 0) : d225276 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d223940, d225276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22164 q selected
    | true =>
      simp only [d223940, d225276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223941 q = 0) : d225277 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d223941, d225277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223941, d225277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223942 q = 0) : d225278 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d223942, d225278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223942, d225278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223943 q = 0) : d225279 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d223943, d225279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223943, d225279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223944 q = 0) : d225280 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d223944, d225280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223944, d225280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223945 q = 0) : d225281 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d223945, d225281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223945, d225281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22166 (p : Pattern) (selected : d223951 p = 0) : d225287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223946 q = 0) : d225282 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d223946, d225282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22165 q selected
    | true =>
      simp only [d223946, d225282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223947 q = 0) : d225283 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d223947, d225283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223947, d225283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223948 q = 0) : d225284 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d223948, d225284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223948, d225284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223949 q = 0) : d225285 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d223949, d225285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223949, d225285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223950 q = 0) : d225286 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d223950, d225286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223950, d225286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223951 q = 0) : d225287 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d223951, d225287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223951, d225287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22167 (p : Pattern) (selected : d223957 p = 0) : d225293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d223952 q = 0) : d225288 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d223952, d225288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22166 q selected
    | true =>
      simp only [d223952, d225288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223953 q = 0) : d225289 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d223953, d225289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223953, d225289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223954 q = 0) : d225290 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d223954, d225290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223954, d225290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223955 q = 0) : d225291 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d223955, d225291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223955, d225291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223956 q = 0) : d225292 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d223956, d225292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223956, d225292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223957 q = 0) : d225293 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d223957, d225293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223957, d225293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22168 (p : Pattern) (selected : d222387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222387 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22169 (p : Pattern) (selected : d222393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222388 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22168 q selected
    | true =>
      simp only [d222388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222390 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222391 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222392 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222393 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22170 (p : Pattern) (selected : d222399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22169 q selected
    | true =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22171 (p : Pattern) (selected : d222405 p = 1) : d225298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222366 q = 1) : d222366 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222372 q = 1) : d222372 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222386 q = 1) : d222386 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d222400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22170 q selected
    | true =>
      simp only [d222400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222401 q = 1) : d225294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222401, d225294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222401, d225294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222294 q = 1) : d222294 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d222402 q = 1) : d225295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222402, d225295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222402, d225295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222403 q = 1) : d225296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222403, d225296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222403, d225296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222404 q = 1) : d225297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222404, d225297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222404, d225297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222405 q = 1) : d225298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222405, d225298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222405, d225298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22172 (p : Pattern) (selected : d222417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22169 q selected
    | true =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22173 (p : Pattern) (selected : d222423 p = 1) : d225303 p = 1 := by
  have h0 (q : Pattern) (selected : d222366 q = 1) : d222366 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222372 q = 1) : d222372 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222386 q = 1) : d222386 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d222400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22170 q selected
    | true =>
      simp only [d222400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222401 q = 1) : d225294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222401, d225294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222401, d225294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222294 q = 1) : d222294 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d222402 q = 1) : d225295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222402, d225295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222402, d225295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222403 q = 1) : d225296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222403, d225296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222403, d225296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222404 q = 1) : d225297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222404, d225297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222404, d225297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222410 q = 1) : d222410 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d222414 q = 1) : d222414 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d222416 q = 1) : d222416 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d222418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22172 q selected
    | true =>
      simp only [d222418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d222419 q = 1) : d225299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222419, d225299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222419, d225299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d222301 q = 1) : d222301 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d222420 q = 1) : d225300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222420, d225300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d222420, d225300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d222421 q = 1) : d225301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222421, d225301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222421, d225301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222422 q = 1) : d225302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222422, d225302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222422, d225302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d222423 q = 1) : d225303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222423, d225303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222423, d225303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22174 (p : Pattern) (selected : d222432 p = 1) : d225310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222416 q = 1) : d222416 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22172 q selected
    | true =>
      simp only [d222418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222419 q = 1) : d225299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222419, d225299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222419, d225299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222301 q = 1) : d222301 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222420 q = 1) : d225300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222420, d225300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222420, d225300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222430 q = 1) : d225308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222430, d225308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222430, d225308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222431 q = 1) : d225309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222431, d225309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222431, d225309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222432 q = 1) : d225310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222432, d225310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222432, d225310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22175 (p : Pattern) (selected : d222452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
  have h2 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116950 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222452 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22176 (p : Pattern) (selected : d222458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22175 q selected
    | true =>
      simp only [d222453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222456 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222457 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222458 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22177 (p : Pattern) (selected : d222464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222459 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22176 q selected
    | true =>
      simp only [d222459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222460 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222461 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222462 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222463 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222464 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22178 (p : Pattern) (selected : d222470 p = 1) : d225320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222451 q = 1) : d222451 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222465 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22177 q selected
    | true =>
      simp only [d222465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d222466 q = 1) : d225316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222466, d225316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222466, d225316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222330 q = 1) : d222330 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222467 q = 1) : d225317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222467, d225317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222467, d225317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222468 q = 1) : d225318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222468, d225318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222468, d225318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222469 q = 1) : d225319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222469, d225319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222469, d225319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222470 q = 1) : d225320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222470, d225320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222470, d225320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22179 (p : Pattern) (selected : d222476 p = 1) : d225326 p = 1 := by
  have h0 (q : Pattern) (selected : d222360 q = 1) : d222360 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222424 q = 1) : d225304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222424, d225304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22171 q selected
    | true =>
      simp only [d222424, d225304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22173 q selected
  have h2 (q : Pattern) (selected : d222426 q = 1) : d222426 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222427 q = 1) : d225305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222427, d225305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222427, d225305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222428 q = 1) : d225306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222428, d225306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222428, d225306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222429 q = 1) : d225307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222429, d225307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222429, d225307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222433 q = 1) : d225311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222433, d225311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222433, d225311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22174 q selected
  have h8 (q : Pattern) (selected : d222434 q = 1) : d225312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222434, d225312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222434, d225312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d222435 q = 1) : d225313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222435, d225313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222435, d225313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d222436 q = 1) : d225314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222436, d225314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222436, d225314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d222437 q = 1) : d225315 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222437, d225315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222437, d225315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222471 q = 1) : d225321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222471, d225321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222471, d225321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22178 q selected
  have h13 (q : Pattern) (selected : d222472 q = 1) : d225322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222472, d225322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222472, d225322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d222473 q = 1) : d225323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222473, d225323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222473, d225323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d222474 q = 1) : d225324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222474, d225324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d222474, d225324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d222475 q = 1) : d225325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222475, d225325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222475, d225325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d222476 q = 1) : d225326 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222476, d225326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222476, d225326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro22180 (p : Pattern) (selected : d222482 p = 1) : d225332 p = 1 := by
  have h0 (q : Pattern) (selected : d222345 q = 1) : d222345 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222477 q = 1) : d225327 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222477, d225327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222477, d225327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22179 q selected
  have h3 (q : Pattern) (selected : d222478 q = 1) : d225328 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222478, d225328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222478, d225328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222479 q = 1) : d225329 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222479, d225329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222479, d225329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222480 q = 1) : d225330 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222480, d225330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222480, d225330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222481 q = 1) : d225331 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222481, d225331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222481, d225331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222482 q = 1) : d225332 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222482, d225332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222482, d225332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22181 (p : Pattern) (selected : d222526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h9 (q : Pattern) (selected : d117030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222526 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22182 (p : Pattern) (selected : d222532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22181 q selected
    | true =>
      simp only [d222527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22168 q selected
  have h2 (q : Pattern) (selected : d222528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222388 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22168 q selected
    | true =>
      simp only [d222388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222390 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222391 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222531 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222532 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22183 (p : Pattern) (selected : d222538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22182 q selected
    | true =>
      simp only [d222533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22169 q selected
    | true =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22184 (p : Pattern) (selected : d222550 p = 1) : d225337 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222503 q = 1) : d222503 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222509 q = 1) : d222509 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222525 q = 1) : d222525 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d222539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22183 q selected
    | true =>
      simp only [d222539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22170 q selected
  have h5 (q : Pattern) (selected : d222540 q = 1) : d225333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222540, d225333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222540, d225333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222546 q = 1) : d222546 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d222547 q = 1) : d225334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222547, d225334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222547, d225334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222548 q = 1) : d225335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222548, d225335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222548, d225335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222549 q = 1) : d225336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222549, d225336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222549, d225336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222550 q = 1) : d225337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222550, d225337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222550, d225337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22185 (p : Pattern) (selected : d222562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22182 q selected
    | true =>
      simp only [d222533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22169 q selected
    | true =>
      simp only [d222394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22186 (p : Pattern) (selected : d222571 p = 1) : d225342 p = 1 := by
  have h0 (q : Pattern) (selected : d222503 q = 1) : d222503 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222509 q = 1) : d222509 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222525 q = 1) : d222525 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22183 q selected
    | true =>
      simp only [d222539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22170 q selected
  have h4 (q : Pattern) (selected : d222540 q = 1) : d225333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222540, d225333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222540, d225333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222546 q = 1) : d222546 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d222547 q = 1) : d225334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222547, d225334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222547, d225334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222548 q = 1) : d225335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222548, d225335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222548, d225335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222549 q = 1) : d225336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222549, d225336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222549, d225336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222555 q = 1) : d222555 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d222559 q = 1) : d222559 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d222561 q = 1) : d222561 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d222563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22185 q selected
    | true =>
      simp only [d222563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22172 q selected
  have h13 (q : Pattern) (selected : d222564 q = 1) : d225338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222564, d225338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222564, d225338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222567 q = 1) : d222567 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d222568 q = 1) : d225339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222568, d225339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222568, d225339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222569 q = 1) : d225340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222569, d225340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222569, d225340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d222570 q = 1) : d225341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222570, d225341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222570, d225341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222571 q = 1) : d225342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222571, d225342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222571, d225342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22187 (p : Pattern) (selected : d222580 p = 1) : d225349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222561 q = 1) : d222561 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22185 q selected
    | true =>
      simp only [d222563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22172 q selected
  have h3 (q : Pattern) (selected : d222564 q = 1) : d225338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222564, d225338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222564, d225338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222567 q = 1) : d222567 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222568 q = 1) : d225339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222568, d225339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222568, d225339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222578 q = 1) : d225347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222578, d225347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222578, d225347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222579 q = 1) : d225348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222579, d225348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222579, d225348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222580 q = 1) : d225349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222580, d225349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222580, d225349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22188 (p : Pattern) (selected : d222604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h2 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h13 (q : Pattern) (selected : d117114 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d116950 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222604 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22189 (p : Pattern) (selected : d222610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22188 q selected
    | true =>
      simp only [d222605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22175 q selected
  have h2 (q : Pattern) (selected : d222606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22175 q selected
    | true =>
      simp only [d222453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222608 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222456 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222609 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222610 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22190 (p : Pattern) (selected : d222616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222611 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22189 q selected
    | true =>
      simp only [d222611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222612 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222459 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22176 q selected
    | true =>
      simp only [d222459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222460 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222613 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222614 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222615 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22191 (p : Pattern) (selected : d222628 p = 1) : d225359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222603 q = 1) : d222603 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22190 q selected
    | true =>
      simp only [d222617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22177 q selected
  have h3 (q : Pattern) (selected : d222618 q = 1) : d225355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222618, d225355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222618, d225355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222624 q = 1) : d222624 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222625 q = 1) : d225356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222625, d225356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222625, d225356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222626 q = 1) : d225357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222626, d225357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222626, d225357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222627 q = 1) : d225358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222627, d225358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222627, d225358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222628 q = 1) : d225359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222628, d225359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222628, d225359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22192 (p : Pattern) (selected : d222640 p = 1) : d225365 p = 1 := by
  have h0 (q : Pattern) (selected : d222497 q = 1) : d222497 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222572 q = 1) : d225343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222572, d225343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22184 q selected
    | true =>
      simp only [d222572, d225343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22186 q selected
  have h2 (q : Pattern) (selected : d222574 q = 1) : d222574 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222575 q = 1) : d225344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222575, d225344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222575, d225344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222576 q = 1) : d225345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222576, d225345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222576, d225345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222577 q = 1) : d225346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222577, d225346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222577, d225346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222581 q = 1) : d225350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222581, d225350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222581, d225350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22187 q selected
  have h8 (q : Pattern) (selected : d222583 q = 1) : d222583 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d222584 q = 1) : d225351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222584, d225351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222584, d225351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222585 q = 1) : d225352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222585, d225352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222585, d225352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d222586 q = 1) : d225353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222586, d225353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222586, d225353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d222587 q = 1) : d225354 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222587, d225354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222587, d225354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222629 q = 1) : d225360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222629, d225360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222629, d225360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22191 q selected
  have h14 (q : Pattern) (selected : d222635 q = 1) : d222635 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d222636 q = 1) : d225361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222636, d225361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222636, d225361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222637 q = 1) : d225362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222637, d225362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222637, d225362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d222638 q = 1) : d225363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222638, d225363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d222638, d225363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d222639 q = 1) : d225364 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222639, d225364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222639, d225364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d222640 q = 1) : d225365 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222640, d225365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222640, d225365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22193 (p : Pattern) (selected : d222646 p = 1) : d225371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222641 q = 1) : d225366 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222641, d225366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222641, d225366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22192 q selected
  have h2 (q : Pattern) (selected : d222642 q = 1) : d225367 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222642, d225367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222642, d225367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222643 q = 1) : d225368 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222643, d225368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222643, d225368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222644 q = 1) : d225369 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222644, d225369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222644, d225369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222645 q = 1) : d225370 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222645, d225370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222645, d225370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222646 q = 1) : d225371 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222646, d225371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222646, d225371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22194 (p : Pattern) (selected : d9659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9655 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6822 q selected
    | true =>
      simp only [d9655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9656 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d9657 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9658 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9659 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro22195 (p : Pattern) (selected : d222740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
    | true =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222734 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22194 q selected
    | true =>
      simp only [d222734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222736 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222737 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222738 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222739 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222740 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22196 (p : Pattern) (selected : d222741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222741 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22197 (p : Pattern) (selected : d222751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222742 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22195 q selected
    | true =>
      simp only [d222742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22196 q selected
  have h2 (q : Pattern) (selected : d222743 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222744 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22196 q selected
    | true =>
      simp only [d222745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222750 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222751 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22198 (p : Pattern) (selected : d222755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222745 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22196 q selected
    | true =>
      simp only [d222745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222746 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222747 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222754 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22199 (p : Pattern) (selected : d222761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22197 q selected
    | true =>
      simp only [d222752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22198 q selected
    | true =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22200 (p : Pattern) (selected : d222765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22198 q selected
    | true =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22201 (p : Pattern) (selected : d222777 p = 1) : d225377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222700 q = 1) : d222700 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222709 q = 1) : d222709 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222733 q = 1) : d222733 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d222766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22199 q selected
    | true =>
      simp only [d222766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22200 q selected
  have h5 (q : Pattern) (selected : d222767 q = 1) : d225373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222767, d225373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222767, d225373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222773 q = 1) : d222773 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d222774 q = 1) : d225374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222774, d225374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222774, d225374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222775 q = 1) : d225375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222775, d225375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222775, d225375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222776 q = 1) : d225376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222776, d225376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222776, d225376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222777 q = 1) : d225377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222777, d225377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222777, d225377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22202 (p : Pattern) (selected : d222791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22197 q selected
    | true =>
      simp only [d222752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22198 q selected
    | true =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222791 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22203 (p : Pattern) (selected : d222792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22198 q selected
    | true =>
      simp only [d222756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222792 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22204 (p : Pattern) (selected : d222801 p = 1) : d225382 p = 1 := by
  have h0 (q : Pattern) (selected : d222700 q = 1) : d222700 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222709 q = 1) : d222709 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222733 q = 1) : d222733 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22199 q selected
    | true =>
      simp only [d222766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22200 q selected
  have h4 (q : Pattern) (selected : d222767 q = 1) : d225373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222767, d225373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222767, d225373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222773 q = 1) : d222773 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d222774 q = 1) : d225374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222774, d225374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222774, d225374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222775 q = 1) : d225375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222775, d225375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222775, d225375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222776 q = 1) : d225376 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222776, d225376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222776, d225376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d222783 q = 1) : d222783 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d222788 q = 1) : d222788 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d222790 q = 1) : d222790 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d222793 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22202 q selected
    | true =>
      simp only [d222793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22203 q selected
  have h13 (q : Pattern) (selected : d222794 q = 1) : d225378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222794, d225378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222794, d225378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222797 q = 1) : d222797 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d222798 q = 1) : d225379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222798, d225379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222798, d225379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222799 q = 1) : d225380 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222799, d225380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222799, d225380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d222800 q = 1) : d225381 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222800, d225381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222800, d225381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d222801 q = 1) : d225382 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222801, d225382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222801, d225382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22205 (p : Pattern) (selected : d222821 p = 1) : d225389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222790 q = 1) : d222790 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222793 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22202 q selected
    | true =>
      simp only [d222793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22203 q selected
  have h3 (q : Pattern) (selected : d222794 q = 1) : d225378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222794, d225378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222794, d225378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222797 q = 1) : d222797 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222798 q = 1) : d225379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222798, d225379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222798, d225379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222819 q = 1) : d225387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222819, d225387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222819, d225387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222820 q = 1) : d225388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222820, d225388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222820, d225388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222821 q = 1) : d225389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222821, d225389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222821, d225389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22206 (p : Pattern) (selected : d222881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
  have h2 (q : Pattern) (selected : d117245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
    | true =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117387 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117388 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22194 q selected
  have h8 (q : Pattern) (selected : d222734 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d222734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22194 q selected
    | true =>
      simp only [d222734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d222735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d222735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d222877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d222877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d222878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d222878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d222879 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d222880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d222880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d222881 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22207 (p : Pattern) (selected : d222882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h2 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117390 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222882 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d222882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22208 (p : Pattern) (selected : d222892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22206 q selected
    | true =>
      simp only [d222883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22207 q selected
  have h2 (q : Pattern) (selected : d222884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22207 q selected
    | true =>
      simp only [d222886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222889 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222890 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d222891 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222892 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22209 (p : Pattern) (selected : d222896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d222886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22207 q selected
    | true =>
      simp only [d222886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d222887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d222888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222890 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d222890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222895 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d222895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222896 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d222896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22210 (p : Pattern) (selected : d222902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222893 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22208 q selected
    | true =>
      simp only [d222893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222894 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22209 q selected
    | true =>
      simp only [d222897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222899 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d222901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d222902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22211 (p : Pattern) (selected : d222906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d222897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22209 q selected
    | true =>
      simp only [d222897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d222898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d222898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222903 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d222903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d222903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d222904 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d222904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d222905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d222905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d222906 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d222906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d222906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22212 (p : Pattern) (selected : d222918 p = 1) : d225399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222874 q = 1) : d222874 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d222907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d222907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22210 q selected
    | true =>
      simp only [d222907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22211 q selected
  have h3 (q : Pattern) (selected : d222908 q = 1) : d225395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d222908, d225395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222908, d225395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222914 q = 1) : d222914 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222915 q = 1) : d225396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d222915, d225396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222915, d225396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222916 q = 1) : d225397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d222916, d225397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222916, d225397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222917 q = 1) : d225398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d222917, d225398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222917, d225398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d222918 q = 1) : d225399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d222918, d225399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222918, d225399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22213 (p : Pattern) (selected : d222935 p = 1) : d225405 p = 1 := by
  have h0 (q : Pattern) (selected : d222692 q = 1) : d222692 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222802 q = 1) : d225383 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222802, d225383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22201 q selected
    | true =>
      simp only [d222802, d225383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22204 q selected
  have h2 (q : Pattern) (selected : d222815 q = 1) : d222815 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d222816 q = 1) : d225384 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222816, d225384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222816, d225384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d222817 q = 1) : d225385 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222817, d225385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d222817, d225385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222818 q = 1) : d225386 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222818, d225386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222818, d225386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d222822 q = 1) : d225390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222822, d225390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222822, d225390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22205 q selected
  have h8 (q : Pattern) (selected : d222824 q = 1) : d222824 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d222825 q = 1) : d225391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222825, d225391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d222825, d225391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d222826 q = 1) : d225392 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222826, d225392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d222826, d225392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d222827 q = 1) : d225393 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222827, d225393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d222827, d225393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d222828 q = 1) : d225394 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222828, d225394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222828, d225394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d222919 q = 1) : d225400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d222919, d225400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d222919, d225400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22212 q selected
  have h14 (q : Pattern) (selected : d222930 q = 1) : d222930 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d222931 q = 1) : d225401 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222931, d225401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d222931, d225401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d222932 q = 1) : d225402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d222932, d225402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d222932, d225402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d222933 q = 1) : d225403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d222933, d225403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d222933, d225403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d222934 q = 1) : d225404 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d222934, d225404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d222934, d225404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d222935 q = 1) : d225405 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d222935, d225405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d222935, d225405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22214 (p : Pattern) (selected : d222941 p = 1) : d225411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222936 q = 1) : d225406 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d222936, d225406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222936, d225406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22213 q selected
  have h2 (q : Pattern) (selected : d222937 q = 1) : d225407 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d222937, d225407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222937, d225407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d222938 q = 1) : d225408 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d222938, d225408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222938, d225408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d222939 q = 1) : d225409 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d222939, d225409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222939, d225409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d222940 q = 1) : d225410 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d222940, d225410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222940, d225410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d222941 q = 1) : d225411 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d222941, d225411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d222941, d225411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22215 (p : Pattern) (selected : d9894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d9890 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6835 q selected
    | true =>
      simp only [d9890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6836 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d9891 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d9892 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9893 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d9894 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h7 p selected
theorem eqIntro22216 (p : Pattern) (selected : d223039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
    | true =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117555 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117556 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223033 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22215 q selected
    | true =>
      simp only [d223033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223034 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223035 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223036 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223037 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117564 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117565 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223038 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223039 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22217 (p : Pattern) (selected : d223040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117559 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117560 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117564 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117565 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117566 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22218 (p : Pattern) (selected : d223044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117564 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117565 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223044 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22219 (p : Pattern) (selected : d223051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22216 q selected
    | true =>
      simp only [d223041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22217 q selected
  have h2 (q : Pattern) (selected : d223042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22217 q selected
    | true =>
      simp only [d223045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22218 q selected
  have h5 (q : Pattern) (selected : d223046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223049 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223050 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223051 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22220 (p : Pattern) (selected : d223055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22217 q selected
    | true =>
      simp only [d223045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22218 q selected
  have h2 (q : Pattern) (selected : d223046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223049 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22221 (p : Pattern) (selected : d223061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22219 q selected
    | true =>
      simp only [d223052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22220 q selected
    | true =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22222 (p : Pattern) (selected : d223065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22220 q selected
    | true =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223062 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223063 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223064 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223065 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22223 (p : Pattern) (selected : d223077 p = 1) : d225418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d222999 q = 1) : d222999 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223008 q = 1) : d223008 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223032 q = 1) : d223032 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d223066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22221 q selected
    | true =>
      simp only [d223066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22222 q selected
  have h5 (q : Pattern) (selected : d223067 q = 1) : d225414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223067, d225414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223067, d225414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223073 q = 1) : d223073 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d223074 q = 1) : d225415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223074, d225415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223074, d225415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223075 q = 1) : d225416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223075, d225416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223075, d225416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223076 q = 1) : d225417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223076, d225417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223076, d225417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223077 q = 1) : d225418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223077, d225418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223077, d225418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22224 (p : Pattern) (selected : d223091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22219 q selected
    | true =>
      simp only [d223052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22220 q selected
    | true =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22225 (p : Pattern) (selected : d223092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22220 q selected
    | true =>
      simp only [d223056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223062 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223063 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223064 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223092 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22226 (p : Pattern) (selected : d223101 p = 1) : d225423 p = 1 := by
  have h0 (q : Pattern) (selected : d222999 q = 1) : d222999 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223008 q = 1) : d223008 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223032 q = 1) : d223032 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22221 q selected
    | true =>
      simp only [d223066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22222 q selected
  have h4 (q : Pattern) (selected : d223067 q = 1) : d225414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223067, d225414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223067, d225414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223073 q = 1) : d223073 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d223074 q = 1) : d225415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223074, d225415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223074, d225415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223075 q = 1) : d225416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223075, d225416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223075, d225416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223076 q = 1) : d225417 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223076, d225417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223076, d225417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223083 q = 1) : d223083 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d223088 q = 1) : d223088 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d223090 q = 1) : d223090 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d223093 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22224 q selected
    | true =>
      simp only [d223093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22225 q selected
  have h13 (q : Pattern) (selected : d223094 q = 1) : d225419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223094, d225419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223094, d225419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d223097 q = 1) : d223097 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223098 q = 1) : d225420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223098, d225420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223098, d225420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223099 q = 1) : d225421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223099, d225421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223099, d225421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d223100 q = 1) : d225422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223100, d225422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223100, d225422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d223101 q = 1) : d225423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223101, d225423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223101, d225423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro22227 (p : Pattern) (selected : d223121 p = 1) : d225430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223090 q = 1) : d223090 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223093 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22224 q selected
    | true =>
      simp only [d223093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22225 q selected
  have h3 (q : Pattern) (selected : d223094 q = 1) : d225419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223094, d225419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223094, d225419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223097 q = 1) : d223097 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223098 q = 1) : d225420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223098, d225420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223098, d225420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223119 q = 1) : d225428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223119, d225428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223119, d225428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223120 q = 1) : d225429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223120, d225429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223120, d225429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223121 q = 1) : d225430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223121, d225430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223121, d225430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22228 (p : Pattern) (selected : d223184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
  have h2 (q : Pattern) (selected : d117553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
    | true =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22215 q selected
  have h8 (q : Pattern) (selected : d223033 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22215 q selected
    | true =>
      simp only [d223033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223034 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d223181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d223181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
  have h15 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d117727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d117728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d223183 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d223184 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22229 (p : Pattern) (selected : d223185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
  have h2 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
  have h8 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117733 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d223185 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22230 (p : Pattern) (selected : d223189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
  have h2 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117733 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223189 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22231 (p : Pattern) (selected : d223196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223186 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22228 q selected
    | true =>
      simp only [d223186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22229 q selected
  have h2 (q : Pattern) (selected : d223187 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223188 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22229 q selected
    | true =>
      simp only [d223190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22230 q selected
  have h5 (q : Pattern) (selected : d223191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223193 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223195 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223196 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22232 (p : Pattern) (selected : d223200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22229 q selected
    | true =>
      simp only [d223190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22230 q selected
  have h2 (q : Pattern) (selected : d223191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223199 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223200 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22233 (p : Pattern) (selected : d223206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223197 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22231 q selected
    | true =>
      simp only [d223197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223198 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22232 q selected
    | true =>
      simp only [d223201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223203 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223204 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223205 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223206 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22234 (p : Pattern) (selected : d223210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223201 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22232 q selected
    | true =>
      simp only [d223201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223202 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22235 (p : Pattern) (selected : d223222 p = 1) : d225440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223177 q = 1) : d223177 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223211 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22233 q selected
    | true =>
      simp only [d223211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22234 q selected
  have h3 (q : Pattern) (selected : d223212 q = 1) : d225436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223212, d225436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223212, d225436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223218 q = 1) : d223218 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223219 q = 1) : d225437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223219, d225437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223219, d225437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223220 q = 1) : d225438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223220, d225438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223220, d225438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223221 q = 1) : d225439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223221, d225439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223221, d225439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223222 q = 1) : d225440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223222, d225440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223222, d225440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22236 (p : Pattern) (selected : d223239 p = 1) : d225446 p = 1 := by
  have h0 (q : Pattern) (selected : d222991 q = 1) : d222991 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223102 q = 1) : d225424 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223102, d225424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22223 q selected
    | true =>
      simp only [d223102, d225424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22226 q selected
  have h2 (q : Pattern) (selected : d223115 q = 1) : d223115 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223116 q = 1) : d225425 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223116, d225425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223116, d225425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d223117 q = 1) : d225426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223117, d225426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223117, d225426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223118 q = 1) : d225427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223118, d225427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223118, d225427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223122 q = 1) : d225431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223122, d225431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223122, d225431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22227 q selected
  have h8 (q : Pattern) (selected : d223124 q = 1) : d223124 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d223125 q = 1) : d225432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223125, d225432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223125, d225432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223126 q = 1) : d225433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223126, d225433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223126, d225433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d223127 q = 1) : d225434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223127, d225434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223127, d225434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d223128 q = 1) : d225435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223128, d225435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223128, d225435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223223 q = 1) : d225441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d223223, d225441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223223, d225441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22235 q selected
  have h14 (q : Pattern) (selected : d223234 q = 1) : d223234 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d223235 q = 1) : d225442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d223235, d225442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d223235, d225442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d223236 q = 1) : d225443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223236, d225443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d223236, d225443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d223237 q = 1) : d225444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d223237, d225444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d223237, d225444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d223238 q = 1) : d225445 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d223238, d225445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d223238, d225445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d223239 q = 1) : d225446 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d223239, d225446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223239, d225446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22237 (p : Pattern) (selected : d223245 p = 1) : d225452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223240 q = 1) : d225447 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d223240, d225447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223240, d225447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22236 q selected
  have h2 (q : Pattern) (selected : d223241 q = 1) : d225448 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d223241, d225448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223241, d225448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223242 q = 1) : d225449 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d223242, d225449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223242, d225449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223243 q = 1) : d225450 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d223243, d225450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223243, d225450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223244 q = 1) : d225451 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d223244, d225451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223244, d225451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223245 q = 1) : d225452 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d223245, d225452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223245, d225452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22238 (p : Pattern) (selected : d10188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10181 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6853 q selected
  have h2 (q : Pattern) (selected : d10182 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10184 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6854 q selected
    | true =>
      simp only [d10184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10185 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10186 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10187 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10188 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro22239 (p : Pattern) (selected : d223354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117911 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
    | true =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117912 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117913 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117914 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223348 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d223348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22238 q selected
    | true =>
      simp only [d223348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223349 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d223349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223350 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d223350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d223351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223352 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117930 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117931 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d223353 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d223353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d223354 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22240 (p : Pattern) (selected : d223356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117917 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117918 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117930 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117931 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d223355 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d223355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117932 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d223356 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d223356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22241 (p : Pattern) (selected : d223360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117930 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117931 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117932 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22242 (p : Pattern) (selected : d223365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117922 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117923 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117937 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223365 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d223365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22243 (p : Pattern) (selected : d223371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223357 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22239 q selected
    | true =>
      simp only [d223357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22240 q selected
  have h2 (q : Pattern) (selected : d223358 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223359 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22240 q selected
    | true =>
      simp only [d223361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22241 q selected
  have h5 (q : Pattern) (selected : d223362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d223364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223366 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22240 q selected
    | true =>
      simp only [d223366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22242 q selected
  have h9 (q : Pattern) (selected : d223367 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223368 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d223369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d223369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d223370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d223371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22244 (p : Pattern) (selected : d223375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223366 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d223366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22240 q selected
    | true =>
      simp only [d223366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22242 q selected
  have h2 (q : Pattern) (selected : d223367 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d223367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223368 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d223368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d223369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d223369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223374 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d223374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223375 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d223375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22245 (p : Pattern) (selected : d223381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22243 q selected
    | true =>
      simp only [d223372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22244 q selected
    | true =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22246 (p : Pattern) (selected : d223385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22244 q selected
    | true =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22247 (p : Pattern) (selected : d223397 p = 1) : d225460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223309 q = 1) : d223309 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d223318 q = 1) : d223318 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d223347 q = 1) : d223347 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d223386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d223386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22245 q selected
    | true =>
      simp only [d223386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22246 q selected
  have h5 (q : Pattern) (selected : d223387 q = 1) : d225456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d223387, d225456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223387, d225456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223393 q = 1) : d223393 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d223394 q = 1) : d225457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d223394, d225457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223394, d225457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d223395 q = 1) : d225458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d223395, d225458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223395, d225458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d223396 q = 1) : d225459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d223396, d225459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d223396, d225459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d223397 q = 1) : d225460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d223397, d225460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223397, d225460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro22248 (p : Pattern) (selected : d223412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22243 q selected
    | true =>
      simp only [d223372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22244 q selected
    | true =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d223378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d223379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d223380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d223380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d223412 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22249 (p : Pattern) (selected : d223413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d223376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22244 q selected
    | true =>
      simp only [d223376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d223377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d223377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d223382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d223382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d223383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d223383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d223383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d223384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d223384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d223384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d223413 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d223413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d223413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
