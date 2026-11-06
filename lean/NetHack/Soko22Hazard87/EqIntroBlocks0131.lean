import NetHack.Soko22Hazard87.EqIntroBlocks0130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro32750 (p : Pattern) (selected : d314266 p = 0) : d315610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314165 q = 0) : d315509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32730 q selected
    | true =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314166 q = 0) : d315510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314167 q = 0) : d315511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314167, d315511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314167, d315511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314168 q = 0) : d315512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314168, d315512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314168, d315512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314265 q = 0) : d315609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314265, d315609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314265, d315609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314266 q = 0) : d315610 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314266, d315610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314266, d315610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32751 (p : Pattern) (selected : d314271 p = 0) : d315615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314159 q = 0) : d315503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32729 q selected
    | true =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314160 q = 0) : d315504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314161 q = 0) : d315505 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314161, d315505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314161, d315505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314162 q = 0) : d315506 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314162, d315506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314162, d315506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314174 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
    | true =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314175 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314176 q = 0) : d315520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314176, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314176, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314177 q = 0) : d315521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314177, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314177, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314270 q = 0) : d315614 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314270, d315614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314270, d315614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314195 q = 0) : d315539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314195, d315539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314195, d315539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314271 q = 0) : d315615 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314271, d315615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314271, d315615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32752 (p : Pattern) (selected : d314277 p = 0) : d315621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314267 q = 0) : d315611 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314267, d315611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32750 q selected
    | true =>
      simp only [d314267, d315611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32732 q selected
  have h2 (q : Pattern) (selected : d314268 q = 0) : d315612 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314268, d315612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314268, d315612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314269 q = 0) : d315613 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314269, d315613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314269, d315613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314272 q = 0) : d315616 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314272, d315616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32732 q selected
    | true =>
      simp only [d314272, d315616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32751 q selected
  have h5 (q : Pattern) (selected : d314273 q = 0) : d315617 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314273, d315617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314273, d315617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314274 q = 0) : d315618 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314274, d315618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314274, d315618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314275 q = 0) : d315619 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314275, d315619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314275, d315619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314197 q = 0) : d315541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314197, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32732 q selected
    | true =>
      simp only [d314197, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32735 q selected
  have h9 (q : Pattern) (selected : d314198 q = 0) : d315542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314198, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314198, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314199 q = 0) : d315543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314199, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314199, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314208 q = 0) : d315552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314208, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32735 q selected
    | true =>
      simp only [d314208, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32737 q selected
  have h12 (q : Pattern) (selected : d314209 q = 0) : d315553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314209, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314209, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314210 q = 0) : d315554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314210, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314210, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314211 q = 0) : d315555 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314211, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314211, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314276 q = 0) : d315620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314276, d315620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314276, d315620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314277 q = 0) : d315621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314277, d315621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314277, d315621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro32753 (p : Pattern) (selected : d314283 p = 0) : d315627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314278 q = 0) : d315622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314278, d315622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32752 q selected
    | true =>
      simp only [d314278, d315622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314279 q = 0) : d315623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314279, d315623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314279, d315623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314215 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32738 q selected
    | true =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314216 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314280 q = 0) : d315624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314280, d315624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314280, d315624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314281 q = 0) : d315625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314281, d315625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314281, d315625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314282 q = 0) : d315626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314282, d315626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314282, d315626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314283 q = 0) : d315627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314283, d315627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314283, d315627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32754 (p : Pattern) (selected : d314289 p = 0) : d315493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314285 q = 0) : d315489 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
    | true =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 0) : d315490 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 0) : d315491 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 0) : d315492 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314289 q = 0) : d315493 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314289, d315493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314289, d315493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32755 (p : Pattern) (selected : d314298 p = 0) : d315502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314285 q = 0) : d315489 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
    | true =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 0) : d315490 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 0) : d315491 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 0) : d315492 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314294 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
    | true =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h6 (q : Pattern) (selected : d314295 q = 0) : d315499 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314296 q = 0) : d315500 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314297 q = 0) : d315501 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314298 q = 0) : d315502 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314298, d315502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314298, d315502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32756 (p : Pattern) (selected : d314304 p = 0) : d315508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314294 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
    | true =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h2 (q : Pattern) (selected : d314295 q = 0) : d315499 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314296 q = 0) : d315500 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314297 q = 0) : d315501 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314304 q = 0) : d315508 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314304, d315508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314304, d315508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32757 (p : Pattern) (selected : d314313 p = 0) : d315517 p = 1 := by
  have h0 (q : Pattern) (selected : d314294 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
    | true =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314295 q = 0) : d315499 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314295, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314296 q = 0) : d315500 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314296, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314297 q = 0) : d315501 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314297, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314309 q = 0) : d315513 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
    | true =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h6 (q : Pattern) (selected : d314310 q = 0) : d315514 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314311 q = 0) : d315515 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314312 q = 0) : d315516 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314313 q = 0) : d315517 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314313, d315517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314313, d315517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32758 (p : Pattern) (selected : d314319 p = 0) : d315523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314290 q = 0) : d315494 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314290, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32754 q selected
    | true =>
      simp only [d314290, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314291 q = 0) : d315495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314291, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314291, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314292 q = 0) : d315496 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314292, d315496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314292, d315496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314293 q = 0) : d315497 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314293, d315497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314293, d315497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314299 q = 0) : d315503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314299, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32755 q selected
    | true =>
      simp only [d314299, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314300 q = 0) : d315504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314300, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314300, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314301 q = 0) : d315505 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314301, d315505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314301, d315505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314302 q = 0) : d315506 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314302, d315506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314302, d315506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314303 q = 0) : d315507 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314303, d315507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314303, d315507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314305 q = 0) : d315509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314305, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32756 q selected
    | true =>
      simp only [d314305, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314306 q = 0) : d315510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314306, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314306, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314307 q = 0) : d315511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314307, d315511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314307, d315511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314308 q = 0) : d315512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314308, d315512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314308, d315512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314314 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
    | true =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314315 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314316 q = 0) : d315520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314316, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314316, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314317 q = 0) : d315521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314317, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314317, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314318 q = 0) : d315522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314318, d315522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314318, d315522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314319 q = 0) : d315523 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314319, d315523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314319, d315523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32759 (p : Pattern) (selected : d314324 p = 0) : d315528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314285 q = 0) : d315489 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
    | true =>
      simp only [d314285, d315489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 0) : d315490 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, d315490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 0) : d315491 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, d315491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 0) : d315492 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, d315492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314294 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
    | true =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h6 (q : Pattern) (selected : d314320 q = 0) : d315524 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314320, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19534 q selected
    | true =>
      simp only [d314320, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314321 q = 0) : d315525 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314321, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314321, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314322 q = 0) : d315526 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314322, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314322, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314323 q = 0) : d315527 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314323, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314323, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314324 q = 0) : d315528 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314324, d315528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314324, d315528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32760 (p : Pattern) (selected : d314329 p = 0) : d315533 p = 1 := by
  have h0 (q : Pattern) (selected : d314294 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19528 q selected
    | true =>
      simp only [d314294, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19445 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314320 q = 0) : d315524 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314320, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19534 q selected
    | true =>
      simp only [d314320, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314321 q = 0) : d315525 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314321, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314321, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314322 q = 0) : d315526 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314322, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314322, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314323 q = 0) : d315527 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314323, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314323, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314309 q = 0) : d315513 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
    | true =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h7 (q : Pattern) (selected : d314310 q = 0) : d315514 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314311 q = 0) : d315515 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314312 q = 0) : d315516 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d314329 q = 0) : d315533 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314329, d315533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314329, d315533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32761 (p : Pattern) (selected : d314336 p = 0) : d315540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314325 q = 0) : d315529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314325, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32759 q selected
    | true =>
      simp only [d314325, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314326 q = 0) : d315530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314326, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314326, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314327 q = 0) : d315531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314327, d315531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314327, d315531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314328 q = 0) : d315532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314328, d315532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314328, d315532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314330 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
    | true =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314331 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314332 q = 0) : d315536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314332, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314332, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314333 q = 0) : d315537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314333, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314333, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314334 q = 0) : d315538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314334, d315538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314334, d315538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314314 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
    | true =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314315 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314316 q = 0) : d315520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314316, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314316, d315520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314317 q = 0) : d315521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314317, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314317, d315521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314335 q = 0) : d315539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314335, d315539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314335, d315539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314336 q = 0) : d315540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314336, d315540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314336, d315540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32762 (p : Pattern) (selected : d314341 p = 0) : d315545 p = 1 := by
  have h0 (q : Pattern) (selected : d314309 q = 0) : d315513 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19531 q selected
    | true =>
      simp only [d314309, d315513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19295 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314310 q = 0) : d315514 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314310, d315514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314311 q = 0) : d315515 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314311, d315515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314312 q = 0) : d315516 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314312, d315516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314341 q = 0) : d315545 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314341, d315545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314341, d315545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro32763 (p : Pattern) (selected : d314347 p = 0) : d315551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314330 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
    | true =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314331 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314332 q = 0) : d315536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314332, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314332, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314333 q = 0) : d315537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314333, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314333, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314340 q = 0) : d315544 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314340, d315544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314340, d315544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314342 q = 0) : d315546 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314342, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32762 q selected
    | true =>
      simp only [d314342, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314343 q = 0) : d315547 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314343, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314343, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314344 q = 0) : d315548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314344, d315548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314344, d315548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314345 q = 0) : d315549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314345, d315549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314345, d315549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314346 q = 0) : d315550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314346, d315550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314346, d315550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314347 q = 0) : d315551 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314347, d315551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314347, d315551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32764 (p : Pattern) (selected : d314354 p = 0) : d315558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314337 q = 0) : d315541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314337, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32758 q selected
    | true =>
      simp only [d314337, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32761 q selected
  have h2 (q : Pattern) (selected : d314338 q = 0) : d315542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314338, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314338, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314339 q = 0) : d315543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314339, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314339, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314348 q = 0) : d315552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314348, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32761 q selected
    | true =>
      simp only [d314348, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32763 q selected
  have h5 (q : Pattern) (selected : d314349 q = 0) : d315553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314349, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314349, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314350 q = 0) : d315554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314350, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314350, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314351 q = 0) : d315555 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314351, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314351, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314352 q = 0) : d315556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314352, d315556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314352, d315556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314353 q = 0) : d315557 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314353, d315557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314353, d315557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314354 q = 0) : d315558 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314354, d315558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314354, d315558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32765 (p : Pattern) (selected : d314358 p = 0) : d315562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314348 q = 0) : d315552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314348, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32761 q selected
    | true =>
      simp only [d314348, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32763 q selected
  have h2 (q : Pattern) (selected : d314349 q = 0) : d315553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314349, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314349, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314350 q = 0) : d315554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314350, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314350, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314352 q = 0) : d315556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314352, d315556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314352, d315556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314357 q = 0) : d315561 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314357, d315561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314357, d315561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314358 q = 0) : d315562 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314358, d315562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314358, d315562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32766 (p : Pattern) (selected : d314364 p = 0) : d315568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314355 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314355, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32764 q selected
    | true =>
      simp only [d314355, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314356 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314356, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314356, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314359 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32765 q selected
    | true =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314360 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314361 q = 0) : d315565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314361, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314361, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314362 q = 0) : d315566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314362, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314362, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314363 q = 0) : d315567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314363, d315567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314363, d315567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314364 q = 0) : d315568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314364, d315568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314364, d315568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32767 (p : Pattern) (selected : d314368 p = 0) : d315572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314359 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32765 q selected
    | true =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314360 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314365 q = 0) : d315569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314365, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314365, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314366 q = 0) : d315570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314366, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314366, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314367 q = 0) : d315571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314367, d315571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314367, d315571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314368 q = 0) : d315572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314368, d315572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314368, d315572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32768 (p : Pattern) (selected : d314374 p = 0) : d315633 p = 1 := by
  have h0 (q : Pattern) (selected : d314154 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314154, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19496 q selected
    | true =>
      simp only [d314154, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19415 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314155 q = 0) : d315499 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314155, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314155, d315499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314156 q = 0) : d315500 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314156, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314156, d315500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314157 q = 0) : d315501 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314157, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314157, d315501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314180 q = 0) : d315524 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314180, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19502 q selected
    | true =>
      simp only [d314180, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314371 q = 0) : d315630 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314371, d315630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314371, d315630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314372 q = 0) : d315631 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314372, d315631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314372, d315631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314373 q = 0) : d315632 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314373, d315632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314373, d315632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314374 q = 0) : d315633 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314374, d315633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314374, d315633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32769 (p : Pattern) (selected : d314380 p = 0) : d315639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314185 q = 0) : d315529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32733 q selected
    | true =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314186 q = 0) : d315530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314187 q = 0) : d315531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314187, d315531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314187, d315531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314188 q = 0) : d315532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314188, d315532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314188, d315532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314190 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
    | true =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314191 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314192 q = 0) : d315536 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314192, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314192, d315536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314193 q = 0) : d315537 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314193, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314193, d315537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314194 q = 0) : d315538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314194, d315538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314194, d315538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314375 q = 0) : d315634 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314375, d315634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32768 q selected
    | true =>
      simp only [d314375, d315634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314376 q = 0) : d315635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314376, d315635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314376, d315635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314377 q = 0) : d315636 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314377, d315636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314377, d315636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314378 q = 0) : d315637 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314378, d315637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314378, d315637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314379 q = 0) : d315638 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314379, d315638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314379, d315638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314380 q = 0) : d315639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314380, d315639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314380, d315639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32770 (p : Pattern) (selected : d314381 p = 0) : d315640 p = 1 := by
  have h0 (q : Pattern) (selected : d314154 q = 0) : d315498 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314154, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19496 q selected
    | true =>
      simp only [d314154, d315498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19415 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314180 q = 0) : d315524 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314180, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19502 q selected
    | true =>
      simp only [d314180, d315524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314181 q = 0) : d315525 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314181, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314181, d315525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314182 q = 0) : d315526 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314182, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314182, d315526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314183 q = 0) : d315527 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314183, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314183, d315527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314371 q = 0) : d315630 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314371, d315630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314371, d315630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314372 q = 0) : d315631 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314372, d315631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314372, d315631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314373 q = 0) : d315632 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314373, d315632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314373, d315632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314381 q = 0) : d315640 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314381, d315640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314381, d315640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32771 (p : Pattern) (selected : d314387 p = 0) : d315646 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314382 q = 0) : d315641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314382, d315641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32770 q selected
    | true =>
      simp only [d314382, d315641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314383 q = 0) : d315642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314383, d315642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314383, d315642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314384 q = 0) : d315643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314384, d315643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314384, d315643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314385 q = 0) : d315644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314385, d315644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314385, d315644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314386 q = 0) : d315645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314386, d315645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314386, d315645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314387 q = 0) : d315646 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314387, d315646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314387, d315646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32772 (p : Pattern) (selected : d314393 p = 0) : d315652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314197 q = 0) : d315541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314197, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32732 q selected
    | true =>
      simp only [d314197, d315541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32735 q selected
  have h2 (q : Pattern) (selected : d314198 q = 0) : d315542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314198, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314198, d315542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314199 q = 0) : d315543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314199, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314199, d315543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314208 q = 0) : d315552 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314208, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32735 q selected
    | true =>
      simp only [d314208, d315552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32737 q selected
  have h5 (q : Pattern) (selected : d314209 q = 0) : d315553 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314209, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314209, d315553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314210 q = 0) : d315554 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314210, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314210, d315554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314211 q = 0) : d315555 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314211, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314211, d315555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314388 q = 0) : d315647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314388, d315647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32769 q selected
    | true =>
      simp only [d314388, d315647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32771 q selected
  have h9 (q : Pattern) (selected : d314389 q = 0) : d315648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314389, d315648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314389, d315648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314390 q = 0) : d315649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314390, d315649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314390, d315649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314391 q = 0) : d315650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314391, d315650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314391, d315650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314392 q = 0) : d315651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314392, d315651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314392, d315651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314393 q = 0) : d315652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314393, d315652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314393, d315652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32773 (p : Pattern) (selected : d314399 p = 0) : d315658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314394 q = 0) : d315653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314394, d315653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32772 q selected
    | true =>
      simp only [d314394, d315653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314395 q = 0) : d315654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314395, d315654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314395, d315654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314396 q = 0) : d315655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314396, d315655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314396, d315655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314397 q = 0) : d315656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314397, d315656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314397, d315656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314398 q = 0) : d315657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314398, d315657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314398, d315657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314399 q = 0) : d315658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314399, d315658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314399, d315658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32774 (p : Pattern) (selected : d314405 p = 0) : d315664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314252 q = 0) : d315596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314252, d315596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32746 q selected
    | true =>
      simp only [d314252, d315596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32747 q selected
  have h2 (q : Pattern) (selected : d314253 q = 0) : d315597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314253, d315597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314253, d315597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314254 q = 0) : d315598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314254, d315598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314254, d315598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314255 q = 0) : d315599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314255, d315599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314255, d315599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314262 q = 0) : d315606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314262, d315606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32748 q selected
    | true =>
      simp only [d314262, d315606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32749 q selected
  have h6 (q : Pattern) (selected : d314263 q = 0) : d315607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314263, d315607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314263, d315607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314264 q = 0) : d315608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314264, d315608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314264, d315608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314284 q = 0) : d315628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314284, d315628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32753 q selected
    | true =>
      simp only [d314284, d315628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32740 q selected
  have h9 (q : Pattern) (selected : d314369 q = 0) : d315573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314369, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32766 q selected
    | true =>
      simp only [d314369, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32767 q selected
  have h10 (q : Pattern) (selected : d314370 q = 0) : d315629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314370, d315629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314370, d315629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314400 q = 0) : d315659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314400, d315659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32773 q selected
    | true =>
      simp only [d314400, d315659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314401 q = 0) : d315660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314401, d315660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314401, d315660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314402 q = 0) : d315661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314402, d315661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314402, d315661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314403 q = 0) : d315662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314403, d315662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314403, d315662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314404 q = 0) : d315663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314404, d315663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314404, d315663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314405 q = 0) : d315664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314405, d315664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314405, d315664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro32775 (p : Pattern) (selected : d314406 p = 0) : d315665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314215 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32738 q selected
    | true =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314216 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314219 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32739 q selected
    | true =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314220 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314221 q = 0) : d315565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314221, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314221, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314222 q = 0) : d315566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314222, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314222, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314248 q = 0) : d315592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314248, d315592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314248, d315592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314406 q = 0) : d315665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314406, d315665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314406, d315665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32776 (p : Pattern) (selected : d314407 p = 0) : d315666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314219 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32739 q selected
    | true =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314220 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314225 q = 0) : d315569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314225, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314225, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314226 q = 0) : d315570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314226, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314226, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314250 q = 0) : d315594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314250, d315594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314250, d315594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314407 q = 0) : d315666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314407, d315666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314407, d315666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32777 (p : Pattern) (selected : d314412 p = 0) : d315671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314215 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32738 q selected
    | true =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314216 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314219 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32739 q selected
    | true =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314220 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314221 q = 0) : d315565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314221, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314221, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314256 q = 0) : d315600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314256, d315600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314256, d315600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314257 q = 0) : d315601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314257, d315601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314257, d315601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314412 q = 0) : d315671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314412, d315671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314412, d315671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32778 (p : Pattern) (selected : d314413 p = 0) : d315672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314219 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32739 q selected
    | true =>
      simp only [d314219, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314220 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314220, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314225 q = 0) : d315569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314225, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314225, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314259 q = 0) : d315603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314259, d315603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314259, d315603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314260 q = 0) : d315604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314260, d315604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314260, d315604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314413 q = 0) : d315672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314413, d315672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314413, d315672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32779 (p : Pattern) (selected : d314417 p = 0) : d315676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314278 q = 0) : d315622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314278, d315622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32752 q selected
    | true =>
      simp only [d314278, d315622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314279 q = 0) : d315623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314279, d315623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314279, d315623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314215 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32738 q selected
    | true =>
      simp only [d314215, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314216 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314216, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314280 q = 0) : d315624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314280, d315624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314280, d315624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314281 q = 0) : d315625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314281, d315625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314281, d315625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314282 q = 0) : d315626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314282, d315626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314282, d315626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314417 q = 0) : d315676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314417, d315676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314417, d315676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32780 (p : Pattern) (selected : d314419 p = 0) : d315581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314355 q = 0) : d315559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314355, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32764 q selected
    | true =>
      simp only [d314355, d315559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314356 q = 0) : d315560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314356, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314356, d315560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314359 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32765 q selected
    | true =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314360 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314361 q = 0) : d315565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314361, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314361, d315565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314362 q = 0) : d315566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314362, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314362, d315566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314363 q = 0) : d315567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314363, d315567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314363, d315567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314419 q = 0) : d315581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314419, d315581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314419, d315581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32781 (p : Pattern) (selected : d314420 p = 0) : d315582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314359 q = 0) : d315563 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32765 q selected
    | true =>
      simp only [d314359, d315563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314360 q = 0) : d315564 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, d315564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314365 q = 0) : d315569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314365, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314365, d315569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314366 q = 0) : d315570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314366, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314366, d315570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314367 q = 0) : d315571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314367, d315571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314367, d315571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314420 q = 0) : d315582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314420, d315582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314420, d315582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32782 (p : Pattern) (selected : d314423 p = 0) : d315679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314394 q = 0) : d315653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314394, d315653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32772 q selected
    | true =>
      simp only [d314394, d315653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314395 q = 0) : d315654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314395, d315654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314395, d315654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314396 q = 0) : d315655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314396, d315655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314396, d315655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314397 q = 0) : d315656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314397, d315656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314397, d315656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314398 q = 0) : d315657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314398, d315657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314398, d315657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314423 q = 0) : d315679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314423, d315679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314423, d315679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32783 (p : Pattern) (selected : d314429 p = 0) : d315685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314252 q = 0) : d315596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314252, d315596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32746 q selected
    | true =>
      simp only [d314252, d315596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32747 q selected
  have h2 (q : Pattern) (selected : d314253 q = 0) : d315597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314253, d315597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314253, d315597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314254 q = 0) : d315598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314254, d315598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314254, d315598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314255 q = 0) : d315599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314255, d315599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314255, d315599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314262 q = 0) : d315606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314262, d315606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32748 q selected
    | true =>
      simp only [d314262, d315606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32749 q selected
  have h6 (q : Pattern) (selected : d314263 q = 0) : d315607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314263, d315607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314263, d315607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314264 q = 0) : d315608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314264, d315608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314264, d315608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314284 q = 0) : d315628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314284, d315628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32753 q selected
    | true =>
      simp only [d314284, d315628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32740 q selected
  have h9 (q : Pattern) (selected : d314369 q = 0) : d315573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314369, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32766 q selected
    | true =>
      simp only [d314369, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32767 q selected
  have h10 (q : Pattern) (selected : d314370 q = 0) : d315629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314370, d315629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314370, d315629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314400 q = 0) : d315659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314400, d315659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32773 q selected
    | true =>
      simp only [d314400, d315659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314401 q = 0) : d315660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314401, d315660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314401, d315660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314402 q = 0) : d315661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314402, d315661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314402, d315661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314403 q = 0) : d315662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314403, d315662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314403, d315662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314404 q = 0) : d315663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314404, d315663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314404, d315663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314408 q = 0) : d315667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314408, d315667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32775 q selected
    | true =>
      simp only [d314408, d315667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32776 q selected
  have h17 (q : Pattern) (selected : d314409 q = 0) : d315668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314409, d315668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314409, d315668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d314410 q = 0) : d315669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314410, d315669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d314410, d315669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d314411 q = 0) : d315670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314411, d315670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314411, d315670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d314414 q = 0) : d315673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314414, d315673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32777 q selected
    | true =>
      simp only [d314414, d315673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32778 q selected
  have h21 (q : Pattern) (selected : d314415 q = 0) : d315674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314415, d315674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314415, d315674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d314416 q = 0) : d315675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314416, d315675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314416, d315675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d314418 q = 0) : d315677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314418, d315677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32779 q selected
    | true =>
      simp only [d314418, d315677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32743 q selected
  have h24 (q : Pattern) (selected : d314421 q = 0) : d315583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314421, d315583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32780 q selected
    | true =>
      simp only [d314421, d315583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32781 q selected
  have h25 (q : Pattern) (selected : d314422 q = 0) : d315678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314422, d315678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d314422, d315678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d314424 q = 0) : d315680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314424, d315680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32782 q selected
    | true =>
      simp only [d314424, d315680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d314425 q = 0) : d315681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314425, d315681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d314425, d315681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d314426 q = 0) : d315682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314426, d315682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d314426, d315682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d314427 q = 0) : d315683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314427, d315683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314427, d315683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d314428 q = 0) : d315684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314428, d315684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314428, d315684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d314429 q = 0) : d315685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314429, d315685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314429, d315685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro32784 (p : Pattern) (selected : d314436 p = 0) : d315692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314229 q = 0) : d315573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314229, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32740 q selected
    | true =>
      simp only [d314229, d315573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32741 q selected
  have h2 (q : Pattern) (selected : d314230 q = 0) : d315574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314230, d315574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314230, d315574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314231 q = 0) : d315575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314231, d315575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314231, d315575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314232 q = 0) : d315576 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314232, d315576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314232, d315576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314233 q = 0) : d315577 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314233, d315577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314233, d315577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314431 q = 0) : d315687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314431, d315687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32741 q selected
    | true =>
      simp only [d314431, d315687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314432 q = 0) : d315688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314432, d315688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314432, d315688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314433 q = 0) : d315689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314433, d315689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314433, d315689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314434 q = 0) : d315690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314434, d315690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314434, d315690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314435 q = 0) : d315691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314435, d315691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314435, d315691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314436 q = 0) : d315692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314436, d315692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314436, d315692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32785 (p : Pattern) (selected : d314442 p = 0) : d315698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314431 q = 0) : d315687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314431, d315687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32741 q selected
    | true =>
      simp only [d314431, d315687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314432 q = 0) : d315688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314432, d315688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314432, d315688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314433 q = 0) : d315689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314433, d315689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314433, d315689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314434 q = 0) : d315690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314434, d315690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314434, d315690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314435 q = 0) : d315691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314435, d315691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314435, d315691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314437 q = 0) : d315693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314437, d315693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32744 q selected
    | true =>
      simp only [d314437, d315693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314438 q = 0) : d315694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314438, d315694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314438, d315694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314439 q = 0) : d315695 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314439, d315695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314439, d315695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314440 q = 0) : d315696 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314440, d315696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314440, d315696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314441 q = 0) : d315697 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314441, d315697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314441, d315697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314442 q = 0) : d315698 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314442, d315698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314442, d315698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32786 (p : Pattern) (selected : d314449 p = 0) : d315705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314418 q = 0) : d315677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314418, d315677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32779 q selected
    | true =>
      simp only [d314418, d315677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32743 q selected
  have h2 (q : Pattern) (selected : d314421 q = 0) : d315583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314421, d315583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32780 q selected
    | true =>
      simp only [d314421, d315583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32781 q selected
  have h3 (q : Pattern) (selected : d314422 q = 0) : d315678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314422, d315678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314422, d315678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314424 q = 0) : d315680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314424, d315680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32782 q selected
    | true =>
      simp only [d314424, d315680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314425 q = 0) : d315681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314425, d315681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314425, d315681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314426 q = 0) : d315682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314426, d315682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314426, d315682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314447 q = 0) : d315703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314447, d315703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314447, d315703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314448 q = 0) : d315704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314448, d315704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314448, d315704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314449 q = 0) : d315705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314449, d315705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314449, d315705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32787 (p : Pattern) (selected : d314451 p = 0) : d315707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314437 q = 0) : d315693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314437, d315693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32744 q selected
    | true =>
      simp only [d314437, d315693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314438 q = 0) : d315694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314438, d315694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314438, d315694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314439 q = 0) : d315695 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314439, d315695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314439, d315695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314440 q = 0) : d315696 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314440, d315696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314440, d315696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314441 q = 0) : d315697 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314441, d315697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314441, d315697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314451 q = 0) : d315707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314451, d315707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314451, d315707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32788 (p : Pattern) (selected : d314462 p = 0) : d315718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314457 q = 0) : d315713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314457, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314457, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32730 q selected
  have h2 (q : Pattern) (selected : d314165 q = 0) : d315509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32730 q selected
    | true =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314458 q = 0) : d315714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314458, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314458, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314166 q = 0) : d315510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314459 q = 0) : d315715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314459, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314459, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314460 q = 0) : d315716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314460, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314460, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314461 q = 0) : d315717 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314461, d315717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314461, d315717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314462 q = 0) : d315718 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314462, d315718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314462, d315718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32789 (p : Pattern) (selected : d314477 p = 0) : d315733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314463 q = 0) : d315719 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314463, d315719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314463, d315719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32728 q selected
  have h2 (q : Pattern) (selected : d314150 q = 0) : d315494 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314150, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32728 q selected
    | true =>
      simp only [d314150, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314464 q = 0) : d315720 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314464, d315720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314464, d315720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314151 q = 0) : d315495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314151, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314151, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314465 q = 0) : d315721 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314465, d315721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314465, d315721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314466 q = 0) : d315722 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314466, d315722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314466, d315722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314467 q = 0) : d315723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314467, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314467, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32729 q selected
  have h8 (q : Pattern) (selected : d314159 q = 0) : d315503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32729 q selected
    | true =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314468 q = 0) : d315724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314468, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314468, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314160 q = 0) : d315504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314469 q = 0) : d315725 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314469, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314469, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314470 q = 0) : d315726 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314470, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314470, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314471 q = 0) : d315727 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314471, d315727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314471, d315727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314457 q = 0) : d315713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314457, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314457, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32730 q selected
  have h15 (q : Pattern) (selected : d314165 q = 0) : d315509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32730 q selected
    | true =>
      simp only [d314165, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314458 q = 0) : d315714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314458, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314458, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314166 q = 0) : d315510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314166, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314459 q = 0) : d315715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314459, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314459, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314460 q = 0) : d315716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314460, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314460, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314472 q = 0) : d315728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
  have h21 (q : Pattern) (selected : d314174 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
    | true =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d314473 q = 0) : d315729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d314175 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d314474 q = 0) : d315730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d314475 q = 0) : d315731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d314476 q = 0) : d315732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314476, d315732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314476, d315732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d314477 q = 0) : d315733 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314477, d315733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314477, d315733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro32790 (p : Pattern) (selected : d314483 p = 0) : d315739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314467 q = 0) : d315723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314467, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314467, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32729 q selected
  have h2 (q : Pattern) (selected : d314159 q = 0) : d315503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32729 q selected
    | true =>
      simp only [d314159, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314468 q = 0) : d315724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314468, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314468, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314160 q = 0) : d315504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314160, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314469 q = 0) : d315725 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314469, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314469, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314470 q = 0) : d315726 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314470, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314470, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314472 q = 0) : d315728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
  have h8 (q : Pattern) (selected : d314174 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
    | true =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314473 q = 0) : d315729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314175 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314474 q = 0) : d315730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314475 q = 0) : d315731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314481 q = 0) : d315737 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314481, d315737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314481, d315737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314482 q = 0) : d315738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314482, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314482, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314483 q = 0) : d315739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314483, d315739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314483, d315739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32791 (p : Pattern) (selected : d314497 p = 0) : d315753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314488 q = 0) : d315744 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314488, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314488, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32733 q selected
  have h2 (q : Pattern) (selected : d314185 q = 0) : d315529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32733 q selected
    | true =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314489 q = 0) : d315745 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314489, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314489, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314186 q = 0) : d315530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314490 q = 0) : d315746 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314490, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314490, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314491 q = 0) : d315747 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314491, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314491, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314492 q = 0) : d315748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
  have h8 (q : Pattern) (selected : d314190 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
    | true =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314493 q = 0) : d315749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314191 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314494 q = 0) : d315750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314495 q = 0) : d315751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314496 q = 0) : d315752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314496, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314496, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314472 q = 0) : d315728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314472, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
  have h15 (q : Pattern) (selected : d314174 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32731 q selected
    | true =>
      simp only [d314174, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314473 q = 0) : d315729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314473, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314175 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314175, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314474 q = 0) : d315730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314474, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314475 q = 0) : d315731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314475, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314482 q = 0) : d315738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314482, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314482, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314497 q = 0) : d315753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314497, d315753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314497, d315753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32792 (p : Pattern) (selected : d314507 p = 0) : d315763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314492 q = 0) : d315748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
  have h2 (q : Pattern) (selected : d314190 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
    | true =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314493 q = 0) : d315749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314191 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314494 q = 0) : d315750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314495 q = 0) : d315751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314501 q = 0) : d315757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314501, d315757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314501, d315757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314502 q = 0) : d315758 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314502, d315758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314502, d315758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32736 q selected
  have h9 (q : Pattern) (selected : d314202 q = 0) : d315546 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314202, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32736 q selected
    | true =>
      simp only [d314202, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314503 q = 0) : d315759 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314503, d315759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314503, d315759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314203 q = 0) : d315547 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314203, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314203, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314504 q = 0) : d315760 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314504, d315760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314504, d315760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314505 q = 0) : d315761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314505, d315761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314505, d315761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314506 q = 0) : d315762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314506, d315762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314506, d315762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314507 q = 0) : d315763 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314507, d315763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314507, d315763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32793 (p : Pattern) (selected : d314513 p = 0) : d315769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314478 q = 0) : d315734 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314478, d315734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32788 q selected
    | true =>
      simp only [d314478, d315734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32789 q selected
  have h2 (q : Pattern) (selected : d314479 q = 0) : d315735 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314479, d315735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314479, d315735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314480 q = 0) : d315736 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314480, d315736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314480, d315736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314484 q = 0) : d315740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314484, d315740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32789 q selected
    | true =>
      simp only [d314484, d315740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32790 q selected
  have h5 (q : Pattern) (selected : d314485 q = 0) : d315741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314485, d315741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314485, d315741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314486 q = 0) : d315742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314486, d315742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314486, d315742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314487 q = 0) : d315743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314487, d315743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314487, d315743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314498 q = 0) : d315754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32789 q selected
    | true =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
  have h9 (q : Pattern) (selected : d314499 q = 0) : d315755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314500 q = 0) : d315756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314508 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
    | true =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32792 q selected
  have h12 (q : Pattern) (selected : d314509 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314510 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314511 q = 0) : d315767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314512 q = 0) : d315768 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314512, d315768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314512, d315768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314513 q = 0) : d315769 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314513, d315769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314513, d315769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro32794 (p : Pattern) (selected : d314518 p = 0) : d315774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314498 q = 0) : d315754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32789 q selected
    | true =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
  have h2 (q : Pattern) (selected : d314499 q = 0) : d315755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314500 q = 0) : d315756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314508 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
    | true =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32792 q selected
  have h5 (q : Pattern) (selected : d314509 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314510 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314511 q = 0) : d315767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314516 q = 0) : d315772 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314516, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314516, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314517 q = 0) : d315773 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314517, d315773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314517, d315773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314518 q = 0) : d315774 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314518, d315774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314518, d315774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32795 (p : Pattern) (selected : d314524 p = 0) : d315780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314514 q = 0) : d315770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314514, d315770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32793 q selected
    | true =>
      simp only [d314514, d315770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314515 q = 0) : d315771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314515, d315771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314515, d315771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314519 q = 0) : d315775 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314519, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32794 q selected
    | true =>
      simp only [d314519, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314520 q = 0) : d315776 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314520, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314520, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314521 q = 0) : d315777 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314521, d315777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314521, d315777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314522 q = 0) : d315778 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314522, d315778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314522, d315778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314523 q = 0) : d315779 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314523, d315779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314523, d315779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314524 q = 0) : d315780 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314524, d315780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314524, d315780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32796 (p : Pattern) (selected : d314526 p = 0) : d315782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314508 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
    | true =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32792 q selected
  have h2 (q : Pattern) (selected : d314509 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314510 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314516 q = 0) : d315772 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314516, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314516, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314525 q = 0) : d315781 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314525, d315781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314525, d315781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314526 q = 0) : d315782 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314526, d315782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314526, d315782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32797 (p : Pattern) (selected : d314532 p = 0) : d315788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314519 q = 0) : d315775 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314519, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32794 q selected
    | true =>
      simp only [d314519, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314520 q = 0) : d315776 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314520, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314520, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314527 q = 0) : d315783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314527, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32796 q selected
    | true =>
      simp only [d314527, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314528 q = 0) : d315784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314528, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314528, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314529 q = 0) : d315785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314529, d315785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314529, d315785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314530 q = 0) : d315786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314530, d315786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314530, d315786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314531 q = 0) : d315787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314531, d315787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314531, d315787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314532 q = 0) : d315788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314532, d315788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314532, d315788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32798 (p : Pattern) (selected : d314552 p = 0) : d315733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314534 q = 0) : d315719 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314534, d315719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314534, d315719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32754 q selected
  have h2 (q : Pattern) (selected : d314290 q = 0) : d315494 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314290, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32754 q selected
    | true =>
      simp only [d314290, d315494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314535 q = 0) : d315720 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314535, d315720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314535, d315720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314291 q = 0) : d315495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314291, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314291, d315495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314536 q = 0) : d315721 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314536, d315721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314536, d315721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314537 q = 0) : d315722 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314537, d315722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314537, d315722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314538 q = 0) : d315723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314538, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314538, d315723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32755 q selected
  have h8 (q : Pattern) (selected : d314299 q = 0) : d315503 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314299, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32755 q selected
    | true =>
      simp only [d314299, d315503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314539 q = 0) : d315724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314539, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314539, d315724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314300 q = 0) : d315504 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314300, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314300, d315504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314540 q = 0) : d315725 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314540, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314540, d315725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314541 q = 0) : d315726 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314541, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314541, d315726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314542 q = 0) : d315727 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314542, d315727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314542, d315727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314543 q = 0) : d315713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314543, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314543, d315713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32756 q selected
  have h15 (q : Pattern) (selected : d314305 q = 0) : d315509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314305, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32756 q selected
    | true =>
      simp only [d314305, d315509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314544 q = 0) : d315714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314544, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314544, d315714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314306 q = 0) : d315510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314306, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314306, d315510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314545 q = 0) : d315715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314545, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314545, d315715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314546 q = 0) : d315716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314546, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314546, d315716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314547 q = 0) : d315728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314547, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314547, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
  have h21 (q : Pattern) (selected : d314314 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
    | true =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d314548 q = 0) : d315729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314548, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d314548, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d314315 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d314549 q = 0) : d315730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314549, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314549, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d314550 q = 0) : d315731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314550, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d314550, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d314551 q = 0) : d315732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314551, d315732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314551, d315732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d314552 q = 0) : d315733 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314552, d315733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314552, d315733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro32799 (p : Pattern) (selected : d314563 p = 0) : d315753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314553 q = 0) : d315744 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314553, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314553, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32759 q selected
  have h2 (q : Pattern) (selected : d314325 q = 0) : d315529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314325, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32759 q selected
    | true =>
      simp only [d314325, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314554 q = 0) : d315745 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314554, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314554, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314326 q = 0) : d315530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314326, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314326, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314555 q = 0) : d315746 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314555, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314555, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314556 q = 0) : d315747 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314556, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314556, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314557 q = 0) : d315748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314557, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314557, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
  have h8 (q : Pattern) (selected : d314330 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
    | true =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314558 q = 0) : d315749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314558, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314558, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314331 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314559 q = 0) : d315750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314559, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314559, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314560 q = 0) : d315751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314560, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314560, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314561 q = 0) : d315752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314561, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314561, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314547 q = 0) : d315728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314547, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314547, d315728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
  have h15 (q : Pattern) (selected : d314314 q = 0) : d315518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32757 q selected
    | true =>
      simp only [d314314, d315518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314548 q = 0) : d315729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314548, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314548, d315729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314315 q = 0) : d315519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314315, d315519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314549 q = 0) : d315730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314549, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314549, d315730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314550 q = 0) : d315731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314550, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314550, d315731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314562 q = 0) : d315738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314562, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314562, d315738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314563 q = 0) : d315753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314563, d315753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314563, d315753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32800 (p : Pattern) (selected : d314573 p = 0) : d315763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314557 q = 0) : d315748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314557, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314557, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
  have h2 (q : Pattern) (selected : d314330 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32760 q selected
    | true =>
      simp only [d314330, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314558 q = 0) : d315749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314558, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314558, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314331 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314331, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314559 q = 0) : d315750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314559, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314559, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314560 q = 0) : d315751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314560, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314560, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314567 q = 0) : d315757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314567, d315757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314567, d315757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314568 q = 0) : d315758 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314568, d315758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314568, d315758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32762 q selected
  have h9 (q : Pattern) (selected : d314342 q = 0) : d315546 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314342, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32762 q selected
    | true =>
      simp only [d314342, d315546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314569 q = 0) : d315759 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314569, d315759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314569, d315759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314343 q = 0) : d315547 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314343, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314343, d315547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314570 q = 0) : d315760 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314570, d315760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314570, d315760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314571 q = 0) : d315761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314571, d315761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314571, d315761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314572 q = 0) : d315762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314572, d315762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314572, d315762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314573 q = 0) : d315763 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314573, d315763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314573, d315763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32801 (p : Pattern) (selected : d314580 p = 0) : d315774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314564 q = 0) : d315754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314564, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32798 q selected
    | true =>
      simp only [d314564, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32799 q selected
  have h2 (q : Pattern) (selected : d314565 q = 0) : d315755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314565, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314565, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314566 q = 0) : d315756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314566, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314566, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314574 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314574, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32799 q selected
    | true =>
      simp only [d314574, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32800 q selected
  have h5 (q : Pattern) (selected : d314575 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314575, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314575, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314576 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314576, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314576, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314577 q = 0) : d315767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314577, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314577, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314578 q = 0) : d315772 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314578, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314578, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314579 q = 0) : d315773 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314579, d315773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314579, d315773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314580 q = 0) : d315774 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314580, d315774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314580, d315774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32802 (p : Pattern) (selected : d314584 p = 0) : d315782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314574 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314574, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32799 q selected
    | true =>
      simp only [d314574, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32800 q selected
  have h2 (q : Pattern) (selected : d314575 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314575, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314575, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314576 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314576, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314576, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314578 q = 0) : d315772 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314578, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314578, d315772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314583 q = 0) : d315781 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314583, d315781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314583, d315781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314584 q = 0) : d315782 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314584, d315782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314584, d315782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32803 (p : Pattern) (selected : d314590 p = 0) : d315788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314581 q = 0) : d315775 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314581, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32801 q selected
    | true =>
      simp only [d314581, d315775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314582 q = 0) : d315776 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314582, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314582, d315776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314585 q = 0) : d315783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314585, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32802 q selected
    | true =>
      simp only [d314585, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314586 q = 0) : d315784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314586, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314586, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314587 q = 0) : d315785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314587, d315785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314587, d315785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314588 q = 0) : d315786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314588, d315786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314588, d315786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314589 q = 0) : d315787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314589, d315787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314589, d315787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314590 q = 0) : d315788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314590, d315788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314590, d315788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32804 (p : Pattern) (selected : d314594 p = 0) : d315793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314585 q = 0) : d315783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314585, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32802 q selected
    | true =>
      simp only [d314585, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314586 q = 0) : d315784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314586, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314586, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314591 q = 0) : d315790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314591, d315790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314591, d315790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314592 q = 0) : d315791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314592, d315791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314592, d315791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314593 q = 0) : d315792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314593, d315792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314593, d315792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314594 q = 0) : d315793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314594, d315793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314594, d315793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32805 (p : Pattern) (selected : d314602 p = 0) : d315801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314488 q = 0) : d315744 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314488, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314488, d315744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32733 q selected
  have h2 (q : Pattern) (selected : d314185 q = 0) : d315529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32733 q selected
    | true =>
      simp only [d314185, d315529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314489 q = 0) : d315745 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314489, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314489, d315745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314186 q = 0) : d315530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314186, d315530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314490 q = 0) : d315746 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314490, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314490, d315746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314491 q = 0) : d315747 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314491, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314491, d315747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314492 q = 0) : d315748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314492, d315748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
  have h8 (q : Pattern) (selected : d314190 q = 0) : d315534 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32734 q selected
    | true =>
      simp only [d314190, d315534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314493 q = 0) : d315749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314493, d315749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314191 q = 0) : d315535 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314191, d315535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314494 q = 0) : d315750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314494, d315750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314495 q = 0) : d315751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314495, d315751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314496 q = 0) : d315752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314496, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314496, d315752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314597 q = 0) : d315796 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314597, d315796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314597, d315796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32768 q selected
  have h15 (q : Pattern) (selected : d314375 q = 0) : d315634 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314375, d315634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32768 q selected
    | true =>
      simp only [d314375, d315634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314598 q = 0) : d315797 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314598, d315797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314598, d315797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314376 q = 0) : d315635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314376, d315635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314376, d315635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314599 q = 0) : d315798 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314599, d315798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314599, d315798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314600 q = 0) : d315799 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314600, d315799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314600, d315799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314601 q = 0) : d315800 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314601, d315800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314601, d315800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314602 q = 0) : d315801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314602, d315801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314602, d315801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32806 (p : Pattern) (selected : d314608 p = 0) : d315807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314603 q = 0) : d315802 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314603, d315802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314603, d315802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32770 q selected
  have h2 (q : Pattern) (selected : d314382 q = 0) : d315641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314382, d315641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32770 q selected
    | true =>
      simp only [d314382, d315641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314604 q = 0) : d315803 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314604, d315803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314604, d315803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314383 q = 0) : d315642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314383, d315642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314383, d315642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314605 q = 0) : d315804 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314605, d315804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314605, d315804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314606 q = 0) : d315805 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314606, d315805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314606, d315805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314607 q = 0) : d315806 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314607, d315806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314607, d315806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314608 q = 0) : d315807 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314608, d315807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314608, d315807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32807 (p : Pattern) (selected : d314614 p = 0) : d315813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314498 q = 0) : d315754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32789 q selected
    | true =>
      simp only [d314498, d315754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
  have h2 (q : Pattern) (selected : d314499 q = 0) : d315755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314499, d315755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314500 q = 0) : d315756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314500, d315756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314508 q = 0) : d315764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32791 q selected
    | true =>
      simp only [d314508, d315764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32792 q selected
  have h5 (q : Pattern) (selected : d314509 q = 0) : d315765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314509, d315765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314510 q = 0) : d315766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314510, d315766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314511 q = 0) : d315767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314511, d315767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314609 q = 0) : d315808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314609, d315808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32805 q selected
    | true =>
      simp only [d314609, d315808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32806 q selected
  have h9 (q : Pattern) (selected : d314610 q = 0) : d315809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314610, d315809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314610, d315809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314611 q = 0) : d315810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314611, d315810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314611, d315810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314612 q = 0) : d315811 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314612, d315811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314612, d315811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314613 q = 0) : d315812 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314613, d315812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314613, d315812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314614 q = 0) : d315813 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314614, d315813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314614, d315813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32808 (p : Pattern) (selected : d314620 p = 0) : d315819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314615 q = 0) : d315814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314615, d315814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32807 q selected
    | true =>
      simp only [d314615, d315814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314616 q = 0) : d315815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314616, d315815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314616, d315815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314617 q = 0) : d315816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314617, d315816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314617, d315816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314618 q = 0) : d315817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314618, d315817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314618, d315817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314619 q = 0) : d315818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314619, d315818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314619, d315818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314620 q = 0) : d315819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314620, d315819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314620, d315819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32809 (p : Pattern) (selected : d314626 p = 0) : d315825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314533 q = 0) : d315789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314533, d315789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32795 q selected
    | true =>
      simp only [d314533, d315789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32797 q selected
  have h2 (q : Pattern) (selected : d314595 q = 0) : d315794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314595, d315794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32803 q selected
    | true =>
      simp only [d314595, d315794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32804 q selected
  have h3 (q : Pattern) (selected : d314596 q = 0) : d315795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314596, d315795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314596, d315795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314621 q = 0) : d315820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314621, d315820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32808 q selected
    | true =>
      simp only [d314621, d315820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314622 q = 0) : d315821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314622, d315821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314622, d315821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314623 q = 0) : d315822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314623, d315822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314623, d315822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314624 q = 0) : d315823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314624, d315823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314624, d315823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314625 q = 0) : d315824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314625, d315824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314625, d315824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314626 q = 0) : d315825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314626, d315825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314626, d315825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32810 (p : Pattern) (selected : d314631 p = 0) : d315793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314527 q = 0) : d315783 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314527, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32796 q selected
    | true =>
      simp only [d314527, d315783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314528 q = 0) : d315784 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314528, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314528, d315784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314628 q = 0) : d315790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314628, d315790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314628, d315790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314629 q = 0) : d315791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314629, d315791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314629, d315791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314630 q = 0) : d315792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314630, d315792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314630, d315792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314631 q = 0) : d315793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314631, d315793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314631, d315793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32811 (p : Pattern) (selected : d314637 p = 0) : d315832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314632 q = 0) : d315827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314632, d315827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32810 q selected
    | true =>
      simp only [d314632, d315827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314633 q = 0) : d315828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314633, d315828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314633, d315828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314634 q = 0) : d315829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314634, d315829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314634, d315829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314635 q = 0) : d315830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314635, d315830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314635, d315830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314636 q = 0) : d315831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314636, d315831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314636, d315831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314637 q = 0) : d315832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314637, d315832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314637, d315832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32812 (p : Pattern) (selected : d314643 p = 0) : d315838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314235 q = 0) : d315579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314235, d315579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314235, d315579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32742 q selected
  have h2 (q : Pattern) (selected : d314236 q = 0) : d315580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314236, d315580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314236, d315580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314245 q = 0) : d315589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314245, d315589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32742 q selected
    | true =>
      simp only [d314245, d315589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32745 q selected
  have h4 (q : Pattern) (selected : d314246 q = 0) : d315590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314246, d315590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314246, d315590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314247 q = 0) : d315591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314247, d315591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314247, d315591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314430 q = 0) : d315686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314430, d315686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32774 q selected
    | true =>
      simp only [d314430, d315686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32783 q selected
  have h7 (q : Pattern) (selected : d314443 q = 0) : d315699 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314443, d315699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32784 q selected
    | true =>
      simp only [d314443, d315699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32785 q selected
  have h8 (q : Pattern) (selected : d314444 q = 0) : d315700 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314444, d315700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314444, d315700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314445 q = 0) : d315701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314445, d315701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314445, d315701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314446 q = 0) : d315702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314446, d315702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314446, d315702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314450 q = 0) : d315706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314450, d315706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314450, d315706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32786 q selected
  have h12 (q : Pattern) (selected : d314452 q = 0) : d315708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314452, d315708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314452, d315708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32787 q selected
  have h13 (q : Pattern) (selected : d314453 q = 0) : d315709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314453, d315709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314453, d315709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314454 q = 0) : d315710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314454, d315710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314454, d315710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314455 q = 0) : d315711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314455, d315711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314455, d315711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314456 q = 0) : d315712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314456, d315712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314456, d315712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314627 q = 0) : d315826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314627, d315826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314627, d315826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32809 q selected
  have h18 (q : Pattern) (selected : d314638 q = 0) : d315833 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314638, d315833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314638, d315833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32811 q selected
  have h19 (q : Pattern) (selected : d314639 q = 0) : d315834 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314639, d315834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d314639, d315834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d314640 q = 0) : d315835 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314640, d315835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314640, d315835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314641 q = 0) : d315836 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314641, d315836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d314641, d315836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d314642 q = 0) : d315837 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314642, d315837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314642, d315837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d314643 q = 0) : d315838 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d314643, d315838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314643, d315838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro32813 (p : Pattern) (selected : d314649 p = 0) : d315844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314644 q = 0) : d315839 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d314644, d315839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314644, d315839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32812 q selected
  have h2 (q : Pattern) (selected : d314645 q = 0) : d315840 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d314645, d315840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314645, d315840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314646 q = 0) : d315841 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d314646, d315841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314646, d315841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314647 q = 0) : d315842 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d314647, d315842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314647, d315842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314648 q = 0) : d315843 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d314648, d315843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314648, d315843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314649 q = 0) : d315844 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d314649, d315844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314649, d315844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32814 (p : Pattern) (selected : d314658 p = 0) : d315853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h2 (q : Pattern) (selected : d314655 q = 0) : d315850 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314656 q = 0) : d315851 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314657 q = 0) : d315852 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314658 q = 0) : d315853 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314658, d315853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314658, d315853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32815 (p : Pattern) (selected : d314668 p = 0) : d315863 p = 1 := by
  have h0 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314655 q = 0) : d315850 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314656 q = 0) : d315851 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314657 q = 0) : d315852 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314664 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
    | true =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h6 (q : Pattern) (selected : d314665 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314666 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314667 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314668 q = 0) : d315863 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314668, d315863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314668, d315863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32816 (p : Pattern) (selected : d314674 p = 0) : d315869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314661 q = 0) : d315856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314662 q = 0) : d315857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314663 q = 0) : d315858 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314663, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314663, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314671 q = 0) : d315866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314672 q = 0) : d315867 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314673 q = 0) : d315868 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314673, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314673, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314674 q = 0) : d315869 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314674, d315869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314674, d315869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32817 (p : Pattern) (selected : d314679 p = 0) : d315874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h2 (q : Pattern) (selected : d314675 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19591 q selected
    | true =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314676 q = 0) : d315871 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314677 q = 0) : d315872 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314678 q = 0) : d315873 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314679 q = 0) : d315874 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314679, d315874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314679, d315874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32818 (p : Pattern) (selected : d314684 p = 0) : d315879 p = 1 := by
  have h0 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314675 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19591 q selected
    | true =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314676 q = 0) : d315871 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314677 q = 0) : d315872 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314678 q = 0) : d315873 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314664 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
    | true =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h7 (q : Pattern) (selected : d314665 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314666 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314667 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d314684 q = 0) : d315879 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314684, d315879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314684, d315879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32819 (p : Pattern) (selected : d314691 p = 0) : d315886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314680 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
    | true =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314681 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314682 q = 0) : d315877 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314682, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314682, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314683 q = 0) : d315878 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314683, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314683, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314687 q = 0) : d315882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314688 q = 0) : d315883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314689 q = 0) : d315884 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314689, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314689, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314671 q = 0) : d315866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314672 q = 0) : d315867 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314690 q = 0) : d315885 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314690, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314690, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314691 q = 0) : d315886 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314691, d315886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314691, d315886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32820 (p : Pattern) (selected : d314696 p = 0) : d315891 p = 1 := by
  have h0 (q : Pattern) (selected : d314664 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19586 q selected
    | true =>
      simp only [d314664, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19587 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314665 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314665, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314666 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314666, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314667 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314667, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314696 q = 0) : d315891 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314696, d315891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314696, d315891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro32821 (p : Pattern) (selected : d314702 p = 0) : d315897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314687 q = 0) : d315882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314688 q = 0) : d315883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314695 q = 0) : d315890 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314695, d315890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314695, d315890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314697 q = 0) : d315892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314697, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32820 q selected
    | true =>
      simp only [d314697, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314698 q = 0) : d315893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314698, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314698, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314699 q = 0) : d315894 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314699, d315894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314699, d315894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314700 q = 0) : d315895 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314700, d315895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314700, d315895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314701 q = 0) : d315896 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314701, d315896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314701, d315896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314702 q = 0) : d315897 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314702, d315897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314702, d315897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32822 (p : Pattern) (selected : d314709 p = 0) : d315904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314692 q = 0) : d315887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32816 q selected
    | true =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
  have h2 (q : Pattern) (selected : d314693 q = 0) : d315888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314694 q = 0) : d315889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314703 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
    | true =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32821 q selected
  have h5 (q : Pattern) (selected : d314704 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314705 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314706 q = 0) : d315901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314707 q = 0) : d315902 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314707, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314707, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314708 q = 0) : d315903 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314708, d315903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314708, d315903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314709 q = 0) : d315904 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314709, d315904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314709, d315904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32823 (p : Pattern) (selected : d314713 p = 0) : d315908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314703 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
    | true =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32821 q selected
  have h2 (q : Pattern) (selected : d314704 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314705 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314707 q = 0) : d315902 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314707, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314707, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314712 q = 0) : d315907 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314712, d315907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314712, d315907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314713 q = 0) : d315908 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314713, d315908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314713, d315908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32824 (p : Pattern) (selected : d314719 p = 0) : d315914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314717 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314718 q = 0) : d315913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314718, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314718, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314719 q = 0) : d315914 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314719, d315914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314719, d315914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32825 (p : Pattern) (selected : d314723 p = 0) : d315918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314721 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314722 q = 0) : d315917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314722, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314722, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314723 q = 0) : d315918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314723, d315918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314723, d315918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32826 (p : Pattern) (selected : d314729 p = 0) : d315924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314724 q = 0) : d315919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32824 q selected
    | true =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32825 q selected
  have h2 (q : Pattern) (selected : d314725 q = 0) : d315920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314726 q = 0) : d315921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314727 q = 0) : d315922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314728 q = 0) : d315923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314729 q = 0) : d315924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314729, d315924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314729, d315924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32827 (p : Pattern) (selected : d314732 p = 0) : d315927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314717 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314718 q = 0) : d315913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314718, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314718, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314732 q = 0) : d315927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314732, d315927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314732, d315927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32828 (p : Pattern) (selected : d314733 p = 0) : d315928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314721 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314722 q = 0) : d315917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314722, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314722, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314733 q = 0) : d315928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314733, d315928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314733, d315928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32829 (p : Pattern) (selected : d314739 p = 0) : d315934 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314724 q = 0) : d315919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32824 q selected
    | true =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32825 q selected
  have h2 (q : Pattern) (selected : d314725 q = 0) : d315920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314726 q = 0) : d315921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314727 q = 0) : d315922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314728 q = 0) : d315923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314734 q = 0) : d315929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314734, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32827 q selected
    | true =>
      simp only [d314734, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32828 q selected
  have h7 (q : Pattern) (selected : d314735 q = 0) : d315930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314735, d315930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314735, d315930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314736 q = 0) : d315931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314736, d315931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314736, d315931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314737 q = 0) : d315932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314737, d315932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314737, d315932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314738 q = 0) : d315933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314738, d315933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314738, d315933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314739 q = 0) : d315934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314739, d315934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314739, d315934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32830 (p : Pattern) (selected : d314744 p = 0) : d315939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314717 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314743 q = 0) : d315938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314743, d315938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314743, d315938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314744 q = 0) : d315939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314744, d315939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314744, d315939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32831 (p : Pattern) (selected : d314746 p = 0) : d315941 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314721 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314745 q = 0) : d315940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314745, d315940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314745, d315940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314746 q = 0) : d315941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314746, d315941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314746, d315941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32832 (p : Pattern) (selected : d314753 p = 0) : d315948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314751 q = 0) : d315946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314751, d315946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314751, d315946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314752 q = 0) : d315947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314752, d315947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314752, d315947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314753 q = 0) : d315948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314753, d315948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314753, d315948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32833 (p : Pattern) (selected : d314756 p = 0) : d315951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314754 q = 0) : d315949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314754, d315949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314754, d315949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314755 q = 0) : d315950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314755, d315950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314755, d315950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314756 q = 0) : d315951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314756, d315951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314756, d315951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32834 (p : Pattern) (selected : d314760 p = 0) : d315955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314661 q = 0) : d315856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314662 q = 0) : d315857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314663 q = 0) : d315858 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314663, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314663, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314760 q = 0) : d315955 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314760, d315955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314760, d315955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32835 (p : Pattern) (selected : d314764 p = 0) : d315959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314661 q = 0) : d315856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314661, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314662 q = 0) : d315857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314662, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314671 q = 0) : d315866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314671, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314672 q = 0) : d315867 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314672, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314673 q = 0) : d315868 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314673, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314673, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314690 q = 0) : d315885 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314690, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314690, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314764 q = 0) : d315959 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314764, d315959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314764, d315959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32836 (p : Pattern) (selected : d314770 p = 0) : d315965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314761 q = 0) : d315956 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314761, d315956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32834 q selected
    | true =>
      simp only [d314761, d315956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32816 q selected
  have h2 (q : Pattern) (selected : d314762 q = 0) : d315957 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314762, d315957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314762, d315957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314763 q = 0) : d315958 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314763, d315958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314763, d315958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314765 q = 0) : d315960 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314765, d315960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32816 q selected
    | true =>
      simp only [d314765, d315960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32835 q selected
  have h5 (q : Pattern) (selected : d314766 q = 0) : d315961 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314766, d315961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314766, d315961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314767 q = 0) : d315962 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314767, d315962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314767, d315962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314768 q = 0) : d315963 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314768, d315963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314768, d315963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314692 q = 0) : d315887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32816 q selected
    | true =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
  have h9 (q : Pattern) (selected : d314693 q = 0) : d315888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314694 q = 0) : d315889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314703 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
    | true =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32821 q selected
  have h12 (q : Pattern) (selected : d314704 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314705 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314706 q = 0) : d315901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314769 q = 0) : d315964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314769, d315964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314769, d315964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314770 q = 0) : d315965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314770, d315965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314770, d315965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro32837 (p : Pattern) (selected : d314776 p = 0) : d315971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314771 q = 0) : d315966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314771, d315966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32836 q selected
    | true =>
      simp only [d314771, d315966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314772 q = 0) : d315967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314772, d315967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314772, d315967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314773 q = 0) : d315968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314773, d315968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314773, d315968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314774 q = 0) : d315969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314774, d315969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314774, d315969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314775 q = 0) : d315970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314775, d315970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314775, d315970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314776 q = 0) : d315971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314776, d315971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314776, d315971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32838 (p : Pattern) (selected : d314782 p = 0) : d315853 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314778 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
    | true =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h2 (q : Pattern) (selected : d314779 q = 0) : d315850 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314779, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314779, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314780 q = 0) : d315851 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314780, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314780, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314781 q = 0) : d315852 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314781, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314781, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314782 q = 0) : d315853 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314782, d315853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314782, d315853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32839 (p : Pattern) (selected : d314792 p = 0) : d315863 p = 1 := by
  have h0 (q : Pattern) (selected : d314778 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
    | true =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314779 q = 0) : d315850 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314779, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314779, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314780 q = 0) : d315851 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314780, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314780, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314781 q = 0) : d315852 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314781, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314781, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314788 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
    | true =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h6 (q : Pattern) (selected : d314789 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314790 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314791 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314792 q = 0) : d315863 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314792, d315863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314792, d315863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32840 (p : Pattern) (selected : d314798 p = 0) : d315869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314783 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314783, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32838 q selected
    | true =>
      simp only [d314783, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314784 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314784, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314784, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314785 q = 0) : d315856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314785, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314785, d315856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314786 q = 0) : d315857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314786, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314786, d315857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314787 q = 0) : d315858 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314787, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314787, d315858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314793 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
    | true =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314794 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314795 q = 0) : d315866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314795, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314795, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314796 q = 0) : d315867 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314796, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314796, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314797 q = 0) : d315868 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314797, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314797, d315868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314798 q = 0) : d315869 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314798, d315869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314798, d315869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32841 (p : Pattern) (selected : d314803 p = 0) : d315874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314778 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
    | true =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h2 (q : Pattern) (selected : d314799 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314799, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19621 q selected
    | true =>
      simp only [d314799, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314800 q = 0) : d315871 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314800, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314800, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314801 q = 0) : d315872 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314801, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314801, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314802 q = 0) : d315873 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314802, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314802, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314803 q = 0) : d315874 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314803, d315874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314803, d315874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32842 (p : Pattern) (selected : d314808 p = 0) : d315879 p = 1 := by
  have h0 (q : Pattern) (selected : d314778 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19612 q selected
    | true =>
      simp only [d314778, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19613 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314799 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314799, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19621 q selected
    | true =>
      simp only [d314799, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314800 q = 0) : d315871 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314800, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314800, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314801 q = 0) : d315872 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314801, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314801, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314802 q = 0) : d315873 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314802, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314802, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314788 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
    | true =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h7 (q : Pattern) (selected : d314789 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314790 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314791 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d314808 q = 0) : d315879 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314808, d315879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314808, d315879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32843 (p : Pattern) (selected : d314815 p = 0) : d315886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314804 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314804, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32841 q selected
    | true =>
      simp only [d314804, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314805 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314805, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314805, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314806 q = 0) : d315877 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314806, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314806, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314807 q = 0) : d315878 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314807, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314807, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314809 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
    | true =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314810 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314811 q = 0) : d315882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314811, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314811, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314812 q = 0) : d315883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314812, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314812, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314813 q = 0) : d315884 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314813, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314813, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314793 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
    | true =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314794 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314795 q = 0) : d315866 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314795, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314795, d315866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314796 q = 0) : d315867 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314796, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314796, d315867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314814 q = 0) : d315885 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314814, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314814, d315885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314815 q = 0) : d315886 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314815, d315886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314815, d315886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32844 (p : Pattern) (selected : d314820 p = 0) : d315891 p = 1 := by
  have h0 (q : Pattern) (selected : d314788 q = 0) : d315859 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19616 q selected
    | true =>
      simp only [d314788, d315859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19617 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314789 q = 0) : d315860 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314789, d315860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314790 q = 0) : d315861 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314790, d315861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314791 q = 0) : d315862 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314791, d315862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314820 q = 0) : d315891 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314820, d315891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314820, d315891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro32845 (p : Pattern) (selected : d314826 p = 0) : d315897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314809 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
    | true =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314810 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314811 q = 0) : d315882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314811, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314811, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314812 q = 0) : d315883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314812, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314812, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314819 q = 0) : d315890 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314819, d315890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314819, d315890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314821 q = 0) : d315892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314821, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32844 q selected
    | true =>
      simp only [d314821, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314822 q = 0) : d315893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314822, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314822, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314823 q = 0) : d315894 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314823, d315894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314823, d315894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314824 q = 0) : d315895 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314824, d315895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314824, d315895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314825 q = 0) : d315896 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314825, d315896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314825, d315896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314826 q = 0) : d315897 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314826, d315897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314826, d315897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32846 (p : Pattern) (selected : d314833 p = 0) : d315904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314816 q = 0) : d315887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314816, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32840 q selected
    | true =>
      simp only [d314816, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32843 q selected
  have h2 (q : Pattern) (selected : d314817 q = 0) : d315888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314817, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314817, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314818 q = 0) : d315889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314818, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314818, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314827 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314827, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32843 q selected
    | true =>
      simp only [d314827, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32845 q selected
  have h5 (q : Pattern) (selected : d314828 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314828, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314828, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314829 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314829, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314829, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314830 q = 0) : d315901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314830, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314830, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314831 q = 0) : d315902 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314831, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314831, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314832 q = 0) : d315903 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314832, d315903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314832, d315903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314833 q = 0) : d315904 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314833, d315904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314833, d315904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32847 (p : Pattern) (selected : d314837 p = 0) : d315908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314827 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314827, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32843 q selected
    | true =>
      simp only [d314827, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32845 q selected
  have h2 (q : Pattern) (selected : d314828 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314828, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314828, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314829 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314829, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314829, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314831 q = 0) : d315902 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314831, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314831, d315902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314836 q = 0) : d315907 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314836, d315907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314836, d315907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314837 q = 0) : d315908 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314837, d315908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314837, d315908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32848 (p : Pattern) (selected : d314843 p = 0) : d315914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314834 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314834, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32846 q selected
    | true =>
      simp only [d314834, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314835 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314835, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314835, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314838 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32847 q selected
    | true =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314839 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314840 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314840, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314840, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314841 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314841, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314841, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314842 q = 0) : d315913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314842, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314842, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314843 q = 0) : d315914 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314843, d315914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314843, d315914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32849 (p : Pattern) (selected : d314847 p = 0) : d315918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314838 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32847 q selected
    | true =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314839 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314844 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314844, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314844, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314845 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314845, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314845, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314846 q = 0) : d315917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314846, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314846, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314847 q = 0) : d315918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314847, d315918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314847, d315918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32850 (p : Pattern) (selected : d314853 p = 0) : d315977 p = 1 := by
  have h0 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314655 q = 0) : d315850 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314655, d315850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314656 q = 0) : d315851 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314656, d315851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314657 q = 0) : d315852 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314657, d315852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314675 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19591 q selected
    | true =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314850 q = 0) : d315974 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314850, d315974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314850, d315974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314851 q = 0) : d315975 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314851, d315975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314851, d315975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314852 q = 0) : d315976 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314852, d315976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314852, d315976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314853 q = 0) : d315977 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314853, d315977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314853, d315977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32851 (p : Pattern) (selected : d314859 p = 0) : d315983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314680 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
    | true =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314681 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314682 q = 0) : d315877 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314682, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314682, d315877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314683 q = 0) : d315878 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314683, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314683, d315878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314687 q = 0) : d315882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314687, d315882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314688 q = 0) : d315883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314688, d315883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314689 q = 0) : d315884 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314689, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314689, d315884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314854 q = 0) : d315978 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314854, d315978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32850 q selected
    | true =>
      simp only [d314854, d315978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314855 q = 0) : d315979 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314855, d315979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314855, d315979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314856 q = 0) : d315980 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314856, d315980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314856, d315980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314857 q = 0) : d315981 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314857, d315981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314857, d315981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314858 q = 0) : d315982 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314858, d315982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314858, d315982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314859 q = 0) : d315983 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314859, d315983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314859, d315983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32852 (p : Pattern) (selected : d314860 p = 0) : d315984 p = 1 := by
  have h0 (q : Pattern) (selected : d314654 q = 0) : d315849 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19582 q selected
    | true =>
      simp only [d314654, d315849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19583 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d314675 q = 0) : d315870 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19591 q selected
    | true =>
      simp only [d314675, d315870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314676 q = 0) : d315871 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314676, d315871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314677 q = 0) : d315872 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314677, d315872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314678 q = 0) : d315873 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314678, d315873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314850 q = 0) : d315974 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314850, d315974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314850, d315974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314851 q = 0) : d315975 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314851, d315975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314851, d315975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314852 q = 0) : d315976 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314852, d315976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314852, d315976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314860 q = 0) : d315984 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314860, d315984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314860, d315984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32853 (p : Pattern) (selected : d314866 p = 0) : d315990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314861 q = 0) : d315985 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314861, d315985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32852 q selected
    | true =>
      simp only [d314861, d315985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314862 q = 0) : d315986 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314862, d315986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314862, d315986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314863 q = 0) : d315987 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314863, d315987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314863, d315987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314864 q = 0) : d315988 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314864, d315988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314864, d315988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314865 q = 0) : d315989 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314865, d315989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314865, d315989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314866 q = 0) : d315990 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314866, d315990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314866, d315990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32854 (p : Pattern) (selected : d314872 p = 0) : d315996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314692 q = 0) : d315887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32816 q selected
    | true =>
      simp only [d314692, d315887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
  have h2 (q : Pattern) (selected : d314693 q = 0) : d315888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314693, d315888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314694 q = 0) : d315889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314694, d315889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314703 q = 0) : d315898 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32819 q selected
    | true =>
      simp only [d314703, d315898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32821 q selected
  have h5 (q : Pattern) (selected : d314704 q = 0) : d315899 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314704, d315899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314705 q = 0) : d315900 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314705, d315900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314706 q = 0) : d315901 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314706, d315901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314867 q = 0) : d315991 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314867, d315991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32851 q selected
    | true =>
      simp only [d314867, d315991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32853 q selected
  have h9 (q : Pattern) (selected : d314868 q = 0) : d315992 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314868, d315992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314868, d315992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314869 q = 0) : d315993 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314869, d315993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314869, d315993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314870 q = 0) : d315994 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314870, d315994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314870, d315994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314871 q = 0) : d315995 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314871, d315995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314871, d315995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314872 q = 0) : d315996 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314872, d315996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314872, d315996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32855 (p : Pattern) (selected : d314878 p = 0) : d316002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314873 q = 0) : d315997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314873, d315997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32854 q selected
    | true =>
      simp only [d314873, d315997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314874 q = 0) : d315998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314874, d315998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314874, d315998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314875 q = 0) : d315999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314875, d315999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314875, d315999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314876 q = 0) : d316000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314876, d316000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314876, d316000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314877 q = 0) : d316001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314877, d316001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314877, d316001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314878 q = 0) : d316002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314878, d316002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314878, d316002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32856 (p : Pattern) (selected : d314884 p = 0) : d316008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314747 q = 0) : d315942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314747, d315942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32830 q selected
    | true =>
      simp only [d314747, d315942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32831 q selected
  have h2 (q : Pattern) (selected : d314748 q = 0) : d315943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314748, d315943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314748, d315943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314749 q = 0) : d315944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314749, d315944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314749, d315944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314750 q = 0) : d315945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314750, d315945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314750, d315945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314757 q = 0) : d315952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314757, d315952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32832 q selected
    | true =>
      simp only [d314757, d315952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32833 q selected
  have h6 (q : Pattern) (selected : d314758 q = 0) : d315953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314758, d315953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314758, d315953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314759 q = 0) : d315954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314759, d315954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314759, d315954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314777 q = 0) : d315972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314777, d315972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32837 q selected
    | true =>
      simp only [d314777, d315972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32824 q selected
  have h9 (q : Pattern) (selected : d314848 q = 0) : d315919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314848, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32848 q selected
    | true =>
      simp only [d314848, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32849 q selected
  have h10 (q : Pattern) (selected : d314849 q = 0) : d315973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314849, d315973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314849, d315973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314879 q = 0) : d316003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314879, d316003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32855 q selected
    | true =>
      simp only [d314879, d316003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314880 q = 0) : d316004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314880, d316004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314880, d316004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314881 q = 0) : d316005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314881, d316005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314881, d316005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314882 q = 0) : d316006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314882, d316006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314882, d316006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314883 q = 0) : d316007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314883, d316007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314883, d316007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314884 q = 0) : d316008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314884, d316008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314884, d316008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro32857 (p : Pattern) (selected : d314885 p = 0) : d316009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314717 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314717, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314743 q = 0) : d315938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314743, d315938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314743, d315938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314885 q = 0) : d316009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314885, d316009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314885, d316009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32858 (p : Pattern) (selected : d314886 p = 0) : d316010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314721 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314721, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314745 q = 0) : d315940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314745, d315940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314745, d315940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314886 q = 0) : d316010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314886, d316010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314886, d316010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32859 (p : Pattern) (selected : d314891 p = 0) : d316015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314716 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314716, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314751 q = 0) : d315946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314751, d315946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314751, d315946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314752 q = 0) : d315947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314752, d315947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314752, d315947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314891 q = 0) : d316015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314891, d316015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314891, d316015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32860 (p : Pattern) (selected : d314892 p = 0) : d316016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314714 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32823 q selected
    | true =>
      simp only [d314714, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314715 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314715, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314720 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314720, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314754 q = 0) : d315949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314754, d315949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314754, d315949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314755 q = 0) : d315950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314755, d315950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314755, d315950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314892 q = 0) : d316016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314892, d316016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314892, d316016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32861 (p : Pattern) (selected : d314896 p = 0) : d316020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314771 q = 0) : d315966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314771, d315966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32836 q selected
    | true =>
      simp only [d314771, d315966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314772 q = 0) : d315967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314772, d315967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314772, d315967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314710 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32822 q selected
    | true =>
      simp only [d314710, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314711 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314711, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314773 q = 0) : d315968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314773, d315968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314773, d315968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314774 q = 0) : d315969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314774, d315969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314774, d315969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314775 q = 0) : d315970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314775, d315970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314775, d315970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314896 q = 0) : d316020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314896, d316020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314896, d316020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32862 (p : Pattern) (selected : d314898 p = 0) : d315927 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314834 q = 0) : d315905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314834, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32846 q selected
    | true =>
      simp only [d314834, d315905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314835 q = 0) : d315906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314835, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314835, d315906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314838 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32847 q selected
    | true =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314839 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314840 q = 0) : d315911 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314840, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314840, d315911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314841 q = 0) : d315912 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314841, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314841, d315912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314842 q = 0) : d315913 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314842, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314842, d315913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314898 q = 0) : d315927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314898, d315927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314898, d315927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32863 (p : Pattern) (selected : d314899 p = 0) : d315928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314838 q = 0) : d315909 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32847 q selected
    | true =>
      simp only [d314838, d315909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314839 q = 0) : d315910 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, d315910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314844 q = 0) : d315915 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314844, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314844, d315915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314845 q = 0) : d315916 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314845, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314845, d315916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314846 q = 0) : d315917 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314846, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314846, d315917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314899 q = 0) : d315928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314899, d315928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314899, d315928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32864 (p : Pattern) (selected : d314902 p = 0) : d316023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314873 q = 0) : d315997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314873, d315997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32854 q selected
    | true =>
      simp only [d314873, d315997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314874 q = 0) : d315998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314874, d315998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314874, d315998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314875 q = 0) : d315999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314875, d315999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314875, d315999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314876 q = 0) : d316000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314876, d316000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314876, d316000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314877 q = 0) : d316001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314877, d316001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314877, d316001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314902 q = 0) : d316023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314902, d316023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314902, d316023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32865 (p : Pattern) (selected : d314908 p = 0) : d316029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314747 q = 0) : d315942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314747, d315942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32830 q selected
    | true =>
      simp only [d314747, d315942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32831 q selected
  have h2 (q : Pattern) (selected : d314748 q = 0) : d315943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314748, d315943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314748, d315943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314749 q = 0) : d315944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314749, d315944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314749, d315944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314750 q = 0) : d315945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314750, d315945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314750, d315945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314757 q = 0) : d315952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314757, d315952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32832 q selected
    | true =>
      simp only [d314757, d315952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32833 q selected
  have h6 (q : Pattern) (selected : d314758 q = 0) : d315953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314758, d315953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314758, d315953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314759 q = 0) : d315954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314759, d315954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314759, d315954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314777 q = 0) : d315972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314777, d315972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32837 q selected
    | true =>
      simp only [d314777, d315972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32824 q selected
  have h9 (q : Pattern) (selected : d314848 q = 0) : d315919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314848, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32848 q selected
    | true =>
      simp only [d314848, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32849 q selected
  have h10 (q : Pattern) (selected : d314849 q = 0) : d315973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314849, d315973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314849, d315973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314879 q = 0) : d316003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314879, d316003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32855 q selected
    | true =>
      simp only [d314879, d316003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314880 q = 0) : d316004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314880, d316004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314880, d316004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314881 q = 0) : d316005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314881, d316005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314881, d316005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314882 q = 0) : d316006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314882, d316006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314882, d316006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314883 q = 0) : d316007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314883, d316007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314883, d316007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314887 q = 0) : d316011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314887, d316011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32857 q selected
    | true =>
      simp only [d314887, d316011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32858 q selected
  have h17 (q : Pattern) (selected : d314888 q = 0) : d316012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314888, d316012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314888, d316012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d314889 q = 0) : d316013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314889, d316013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d314889, d316013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d314890 q = 0) : d316014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314890, d316014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314890, d316014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d314893 q = 0) : d316017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314893, d316017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32859 q selected
    | true =>
      simp only [d314893, d316017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32860 q selected
  have h21 (q : Pattern) (selected : d314894 q = 0) : d316018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314894, d316018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314894, d316018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d314895 q = 0) : d316019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314895, d316019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314895, d316019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d314897 q = 0) : d316021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314897, d316021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32861 q selected
    | true =>
      simp only [d314897, d316021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32827 q selected
  have h24 (q : Pattern) (selected : d314900 q = 0) : d315929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314900, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32862 q selected
    | true =>
      simp only [d314900, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32863 q selected
  have h25 (q : Pattern) (selected : d314901 q = 0) : d316022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314901, d316022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d314901, d316022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d314903 q = 0) : d316024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314903, d316024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32864 q selected
    | true =>
      simp only [d314903, d316024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d314904 q = 0) : d316025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314904, d316025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d314904, d316025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d314905 q = 0) : d316026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314905, d316026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d314905, d316026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d314906 q = 0) : d316027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314906, d316027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314906, d316027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d314907 q = 0) : d316028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314907, d316028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314907, d316028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d314908 q = 0) : d316029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314908, d316029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314908, d316029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro32866 (p : Pattern) (selected : d314915 p = 0) : d316036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314724 q = 0) : d315919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32824 q selected
    | true =>
      simp only [d314724, d315919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32825 q selected
  have h2 (q : Pattern) (selected : d314725 q = 0) : d315920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314725, d315920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314726 q = 0) : d315921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314726, d315921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314727 q = 0) : d315922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314727, d315922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314728 q = 0) : d315923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314728, d315923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314910 q = 0) : d316031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314910, d316031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32825 q selected
    | true =>
      simp only [d314910, d316031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314911 q = 0) : d316032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314911, d316032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314911, d316032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314912 q = 0) : d316033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314912, d316033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314912, d316033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314913 q = 0) : d316034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314913, d316034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314913, d316034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314914 q = 0) : d316035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314914, d316035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314914, d316035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314915 q = 0) : d316036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314915, d316036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314915, d316036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32867 (p : Pattern) (selected : d314921 p = 0) : d316042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314910 q = 0) : d316031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314910, d316031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32825 q selected
    | true =>
      simp only [d314910, d316031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314911 q = 0) : d316032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314911, d316032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314911, d316032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314912 q = 0) : d316033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314912, d316033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314912, d316033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314913 q = 0) : d316034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314913, d316034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314913, d316034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314914 q = 0) : d316035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314914, d316035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314914, d316035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314916 q = 0) : d316037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314916, d316037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32828 q selected
    | true =>
      simp only [d314916, d316037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314917 q = 0) : d316038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314917, d316038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314917, d316038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314918 q = 0) : d316039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314918, d316039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314918, d316039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314919 q = 0) : d316040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314919, d316040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314919, d316040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314920 q = 0) : d316041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314920, d316041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314920, d316041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314921 q = 0) : d316042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314921, d316042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314921, d316042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32868 (p : Pattern) (selected : d314928 p = 0) : d316049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314897 q = 0) : d316021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314897, d316021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32861 q selected
    | true =>
      simp only [d314897, d316021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32827 q selected
  have h2 (q : Pattern) (selected : d314900 q = 0) : d315929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314900, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32862 q selected
    | true =>
      simp only [d314900, d315929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32863 q selected
  have h3 (q : Pattern) (selected : d314901 q = 0) : d316022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314901, d316022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314901, d316022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314903 q = 0) : d316024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314903, d316024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32864 q selected
    | true =>
      simp only [d314903, d316024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314904 q = 0) : d316025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314904, d316025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314904, d316025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314905 q = 0) : d316026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314905, d316026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314905, d316026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314926 q = 0) : d316047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314926, d316047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314926, d316047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314927 q = 0) : d316048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314927, d316048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314927, d316048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314928 q = 0) : d316049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314928, d316049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314928, d316049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32869 (p : Pattern) (selected : d314930 p = 0) : d316051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314916 q = 0) : d316037 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314916, d316037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32828 q selected
    | true =>
      simp only [d314916, d316037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314917 q = 0) : d316038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314917, d316038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314917, d316038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314918 q = 0) : d316039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314918, d316039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314918, d316039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314919 q = 0) : d316040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314919, d316040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314919, d316040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314920 q = 0) : d316041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314920, d316041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314920, d316041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314930 q = 0) : d316051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314930, d316051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314930, d316051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32870 (p : Pattern) (selected : d314941 p = 0) : d316062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314936 q = 0) : d316057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
  have h2 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314937 q = 0) : d316058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314938 q = 0) : d316059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314939 q = 0) : d316060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314940 q = 0) : d316061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314940, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314940, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314941 q = 0) : d316062 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314941, d316062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314941, d316062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32871 (p : Pattern) (selected : d314947 p = 0) : d316068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314936 q = 0) : d316057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
  have h2 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314937 q = 0) : d316058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314938 q = 0) : d316059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314939 q = 0) : d316060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314940 q = 0) : d316061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314940, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314940, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314942 q = 0) : d316063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
  have h9 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314943 q = 0) : d316064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314944 q = 0) : d316065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314945 q = 0) : d316066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314946 q = 0) : d316067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314946, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314946, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314947 q = 0) : d316068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314947, d316068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314947, d316068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32872 (p : Pattern) (selected : d314952 p = 0) : d316073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314936 q = 0) : d316057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314936, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
  have h2 (q : Pattern) (selected : d314659 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32814 q selected
    | true =>
      simp only [d314659, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314937 q = 0) : d316058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314937, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314660 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314660, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314938 q = 0) : d316059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314938, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314939 q = 0) : d316060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314939, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314942 q = 0) : d316063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
  have h8 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314943 q = 0) : d316064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314944 q = 0) : d316065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314945 q = 0) : d316066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314946 q = 0) : d316067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314946, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314946, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314951 q = 0) : d316072 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314951, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314951, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314952 q = 0) : d316073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314952, d316073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314952, d316073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32873 (p : Pattern) (selected : d314966 p = 0) : d316087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314957 q = 0) : d316078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314957, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314957, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
  have h2 (q : Pattern) (selected : d314680 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
    | true =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314958 q = 0) : d316079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314958, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314958, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314681 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314959 q = 0) : d316080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314959, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314959, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314960 q = 0) : d316081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314960, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314960, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314961 q = 0) : d316082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
  have h8 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314962 q = 0) : d316083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314963 q = 0) : d316084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314964 q = 0) : d316085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314965 q = 0) : d316086 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314965, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314965, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314942 q = 0) : d316063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314942, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
  have h15 (q : Pattern) (selected : d314669 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32815 q selected
    | true =>
      simp only [d314669, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314943 q = 0) : d316064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314943, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314670 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314670, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314944 q = 0) : d316065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314944, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314945 q = 0) : d316066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314945, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314951 q = 0) : d316072 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314951, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314951, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314966 q = 0) : d316087 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314966, d316087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314966, d316087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32874 (p : Pattern) (selected : d314976 p = 0) : d316097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314961 q = 0) : d316082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
  have h2 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314962 q = 0) : d316083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314963 q = 0) : d316084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314964 q = 0) : d316085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314970 q = 0) : d316091 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314970, d316091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314970, d316091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314971 q = 0) : d316092 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314971, d316092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314971, d316092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32820 q selected
  have h9 (q : Pattern) (selected : d314697 q = 0) : d315892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314697, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32820 q selected
    | true =>
      simp only [d314697, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314972 q = 0) : d316093 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314972, d316093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314972, d316093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314698 q = 0) : d315893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314698, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314698, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314973 q = 0) : d316094 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314973, d316094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314973, d316094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314974 q = 0) : d316095 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314974, d316095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314974, d316095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314975 q = 0) : d316096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314975, d316096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314975, d316096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314976 q = 0) : d316097 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314976, d316097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314976, d316097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32875 (p : Pattern) (selected : d314982 p = 0) : d316103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314948 q = 0) : d316069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314948, d316069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32870 q selected
    | true =>
      simp only [d314948, d316069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32871 q selected
  have h2 (q : Pattern) (selected : d314949 q = 0) : d316070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314949, d316070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314949, d316070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314950 q = 0) : d316071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314950, d316071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314950, d316071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314953 q = 0) : d316074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314953, d316074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32871 q selected
    | true =>
      simp only [d314953, d316074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32872 q selected
  have h5 (q : Pattern) (selected : d314954 q = 0) : d316075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314954, d316075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314954, d316075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314955 q = 0) : d316076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314955, d316076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314955, d316076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314956 q = 0) : d316077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314956, d316077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314956, d316077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314967 q = 0) : d316088 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32871 q selected
    | true =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
  have h9 (q : Pattern) (selected : d314968 q = 0) : d316089 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314969 q = 0) : d316090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314977 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
    | true =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32874 q selected
  have h12 (q : Pattern) (selected : d314978 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314979 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314980 q = 0) : d316101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d314981 q = 0) : d316102 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314981, d316102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314981, d316102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314982 q = 0) : d316103 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314982, d316103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314982, d316103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro32876 (p : Pattern) (selected : d314987 p = 0) : d316108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314967 q = 0) : d316088 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32871 q selected
    | true =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
  have h2 (q : Pattern) (selected : d314968 q = 0) : d316089 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314969 q = 0) : d316090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314977 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
    | true =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32874 q selected
  have h5 (q : Pattern) (selected : d314978 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314979 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314980 q = 0) : d316101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314985 q = 0) : d316106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314985, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314985, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314986 q = 0) : d316107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314986, d316107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314986, d316107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314987 q = 0) : d316108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314987, d316108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314987, d316108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32877 (p : Pattern) (selected : d314993 p = 0) : d316114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314983 q = 0) : d316104 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314983, d316104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32875 q selected
    | true =>
      simp only [d314983, d316104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314984 q = 0) : d316105 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314984, d316105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314984, d316105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314988 q = 0) : d316109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314988, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32876 q selected
    | true =>
      simp only [d314988, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314989 q = 0) : d316110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314989, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314989, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314990 q = 0) : d316111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314990, d316111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314990, d316111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314991 q = 0) : d316112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314991, d316112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314991, d316112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314992 q = 0) : d316113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314992, d316113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314992, d316113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314993 q = 0) : d316114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314993, d316114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314993, d316114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32878 (p : Pattern) (selected : d314995 p = 0) : d316116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314977 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
    | true =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32874 q selected
  have h2 (q : Pattern) (selected : d314978 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314979 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314985 q = 0) : d316106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314985, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314985, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314994 q = 0) : d316115 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314994, d316115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314994, d316115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314995 q = 0) : d316116 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314995, d316116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314995, d316116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32879 (p : Pattern) (selected : d315001 p = 0) : d316122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314988 q = 0) : d316109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314988, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32876 q selected
    | true =>
      simp only [d314988, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314989 q = 0) : d316110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314989, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314989, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314996 q = 0) : d316117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314996, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32878 q selected
    | true =>
      simp only [d314996, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314997 q = 0) : d316118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314997, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314997, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314998 q = 0) : d316119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314998, d316119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314998, d316119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314999 q = 0) : d316120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314999, d316120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314999, d316120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315000 q = 0) : d316121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315000, d316121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315000, d316121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315001 q = 0) : d316122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315001, d316122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315001, d316122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32880 (p : Pattern) (selected : d315013 p = 0) : d316068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315003 q = 0) : d316057 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315003, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315003, d316057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32838 q selected
  have h2 (q : Pattern) (selected : d314783 q = 0) : d315854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314783, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32838 q selected
    | true =>
      simp only [d314783, d315854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315004 q = 0) : d316058 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315004, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315004, d316058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314784 q = 0) : d315855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314784, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314784, d315855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315005 q = 0) : d316059 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315005, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315005, d316059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315006 q = 0) : d316060 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315006, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315006, d316060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315007 q = 0) : d316061 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315007, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315007, d316061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315008 q = 0) : d316063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315008, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315008, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
  have h9 (q : Pattern) (selected : d314793 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
    | true =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d315009 q = 0) : d316064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315009, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d315009, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314794 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d315010 q = 0) : d316065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315010, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d315010, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315011 q = 0) : d316066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315011, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315011, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d315012 q = 0) : d316067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315012, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315012, d316067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d315013 q = 0) : d316068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315013, d316068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315013, d316068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32881 (p : Pattern) (selected : d315024 p = 0) : d316087 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315014 q = 0) : d316078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315014, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315014, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32841 q selected
  have h2 (q : Pattern) (selected : d314804 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314804, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32841 q selected
    | true =>
      simp only [d314804, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315015 q = 0) : d316079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315015, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315015, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314805 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314805, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314805, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315016 q = 0) : d316080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315016, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315016, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315017 q = 0) : d316081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315017, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315017, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315018 q = 0) : d316082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315018, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315018, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
  have h8 (q : Pattern) (selected : d314809 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
    | true =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d315019 q = 0) : d316083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315019, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315019, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314810 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d315020 q = 0) : d316084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315020, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d315020, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d315021 q = 0) : d316085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315021, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d315021, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d315022 q = 0) : d316086 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315022, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315022, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d315008 q = 0) : d316063 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315008, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315008, d316063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
  have h15 (q : Pattern) (selected : d314793 q = 0) : d315864 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32839 q selected
    | true =>
      simp only [d314793, d315864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d315009 q = 0) : d316064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315009, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d315009, d316064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314794 q = 0) : d315865 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314794, d315865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d315010 q = 0) : d316065 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315010, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d315010, d316065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d315011 q = 0) : d316066 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315011, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d315011, d316066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d315023 q = 0) : d316072 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315023, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d315023, d316072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d315024 q = 0) : d316087 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315024, d316087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315024, d316087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32882 (p : Pattern) (selected : d315034 p = 0) : d316097 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315018 q = 0) : d316082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315018, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315018, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
  have h2 (q : Pattern) (selected : d314809 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32842 q selected
    | true =>
      simp only [d314809, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315019 q = 0) : d316083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315019, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315019, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314810 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314810, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315020 q = 0) : d316084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315020, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315020, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315021 q = 0) : d316085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315021, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315021, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315028 q = 0) : d316091 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315028, d316091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315028, d316091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315029 q = 0) : d316092 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315029, d316092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315029, d316092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32844 q selected
  have h9 (q : Pattern) (selected : d314821 q = 0) : d315892 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314821, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32844 q selected
    | true =>
      simp only [d314821, d315892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d315030 q = 0) : d316093 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315030, d316093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d315030, d316093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314822 q = 0) : d315893 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314822, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314822, d315893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d315031 q = 0) : d316094 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315031, d316094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d315031, d316094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315032 q = 0) : d316095 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315032, d316095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315032, d316095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d315033 q = 0) : d316096 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315033, d316096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315033, d316096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d315034 q = 0) : d316097 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315034, d316097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315034, d316097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32883 (p : Pattern) (selected : d315041 p = 0) : d316108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315025 q = 0) : d316088 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315025, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32880 q selected
    | true =>
      simp only [d315025, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32881 q selected
  have h2 (q : Pattern) (selected : d315026 q = 0) : d316089 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315026, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315026, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315027 q = 0) : d316090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315027, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315027, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315035 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315035, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32881 q selected
    | true =>
      simp only [d315035, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32882 q selected
  have h5 (q : Pattern) (selected : d315036 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315036, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315036, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315037 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315037, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315037, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d315038 q = 0) : d316101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315038, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315038, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315039 q = 0) : d316106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315039, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315039, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d315040 q = 0) : d316107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315040, d316107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315040, d316107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d315041 q = 0) : d316108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315041, d316108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d315041, d316108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32884 (p : Pattern) (selected : d315045 p = 0) : d316116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315035 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315035, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32881 q selected
    | true =>
      simp only [d315035, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32882 q selected
  have h2 (q : Pattern) (selected : d315036 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315036, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315036, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315037 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315037, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315037, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315039 q = 0) : d316106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315039, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315039, d316106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315044 q = 0) : d316115 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315044, d316115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315044, d316115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315045 q = 0) : d316116 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315045, d316116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315045, d316116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32885 (p : Pattern) (selected : d315051 p = 0) : d316122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315042 q = 0) : d316109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315042, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32883 q selected
    | true =>
      simp only [d315042, d316109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315043 q = 0) : d316110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315043, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315043, d316110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315046 q = 0) : d316117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315046, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32884 q selected
    | true =>
      simp only [d315046, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315047 q = 0) : d316118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315047, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315047, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d315048 q = 0) : d316119 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315048, d316119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315048, d316119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315049 q = 0) : d316120 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315049, d316120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315049, d316120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315050 q = 0) : d316121 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315050, d316121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315050, d316121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315051 q = 0) : d316122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315051, d316122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315051, d316122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32886 (p : Pattern) (selected : d315055 p = 0) : d316127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315046 q = 0) : d316117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315046, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32884 q selected
    | true =>
      simp only [d315046, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315047 q = 0) : d316118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315047, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315047, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315052 q = 0) : d316124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315052, d316124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315052, d316124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315053 q = 0) : d316125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315053, d316125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315053, d316125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315054 q = 0) : d316126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315054, d316126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315054, d316126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315055 q = 0) : d316127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315055, d316127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315055, d316127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32887 (p : Pattern) (selected : d315063 p = 0) : d316135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314957 q = 0) : d316078 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314957, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314957, d316078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
  have h2 (q : Pattern) (selected : d314680 q = 0) : d315875 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32817 q selected
    | true =>
      simp only [d314680, d315875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314958 q = 0) : d316079 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314958, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314958, d316079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314681 q = 0) : d315876 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314681, d315876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314959 q = 0) : d316080 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314959, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314959, d316080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314960 q = 0) : d316081 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314960, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314960, d316081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314961 q = 0) : d316082 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314961, d316082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
  have h8 (q : Pattern) (selected : d314685 q = 0) : d315880 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32818 q selected
    | true =>
      simp only [d314685, d315880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314962 q = 0) : d316083 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314962, d316083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314686 q = 0) : d315881 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314686, d315881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314963 q = 0) : d316084 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314963, d316084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314964 q = 0) : d316085 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314964, d316085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314965 q = 0) : d316086 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314965, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314965, d316086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d315058 q = 0) : d316130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315058, d316130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315058, d316130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32850 q selected
  have h15 (q : Pattern) (selected : d314854 q = 0) : d315978 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314854, d315978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32850 q selected
    | true =>
      simp only [d314854, d315978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d315059 q = 0) : d316131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315059, d316131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d315059, d316131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314855 q = 0) : d315979 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314855, d315979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314855, d315979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d315060 q = 0) : d316132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315060, d316132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d315060, d316132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d315061 q = 0) : d316133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315061, d316133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d315061, d316133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d315062 q = 0) : d316134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315062, d316134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d315062, d316134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d315063 q = 0) : d316135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315063, d316135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315063, d316135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32888 (p : Pattern) (selected : d315069 p = 0) : d316141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315064 q = 0) : d316136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315064, d316136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315064, d316136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32852 q selected
  have h2 (q : Pattern) (selected : d314861 q = 0) : d315985 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314861, d315985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32852 q selected
    | true =>
      simp only [d314861, d315985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315065 q = 0) : d316137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315065, d316137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315065, d316137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314862 q = 0) : d315986 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314862, d315986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314862, d315986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315066 q = 0) : d316138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315066, d316138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315066, d316138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315067 q = 0) : d316139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315067, d316139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315067, d316139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315068 q = 0) : d316140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315068, d316140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315068, d316140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315069 q = 0) : d316141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315069, d316141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315069, d316141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32889 (p : Pattern) (selected : d315075 p = 0) : d316147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314967 q = 0) : d316088 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32871 q selected
    | true =>
      simp only [d314967, d316088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
  have h2 (q : Pattern) (selected : d314968 q = 0) : d316089 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314968, d316089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314969 q = 0) : d316090 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314969, d316090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314977 q = 0) : d316098 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32873 q selected
    | true =>
      simp only [d314977, d316098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32874 q selected
  have h5 (q : Pattern) (selected : d314978 q = 0) : d316099 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314978, d316099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314979 q = 0) : d316100 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314979, d316100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314980 q = 0) : d316101 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314980, d316101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315070 q = 0) : d316142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315070, d316142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32887 q selected
    | true =>
      simp only [d315070, d316142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32888 q selected
  have h9 (q : Pattern) (selected : d315071 q = 0) : d316143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315071, d316143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315071, d316143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d315072 q = 0) : d316144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315072, d316144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315072, d316144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d315073 q = 0) : d316145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315073, d316145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d315073, d316145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d315074 q = 0) : d316146 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315074, d316146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315074, d316146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315075 q = 0) : d316147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315075, d316147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315075, d316147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32890 (p : Pattern) (selected : d315081 p = 0) : d316153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315076 q = 0) : d316148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315076, d316148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32889 q selected
    | true =>
      simp only [d315076, d316148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315077 q = 0) : d316149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315077, d316149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315077, d316149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315078 q = 0) : d316150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315078, d316150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315078, d316150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315079 q = 0) : d316151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315079, d316151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315079, d316151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315080 q = 0) : d316152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315080, d316152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315080, d316152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315081 q = 0) : d316153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315081, d316153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315081, d316153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32891 (p : Pattern) (selected : d315087 p = 0) : d316159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315002 q = 0) : d316123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315002, d316123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32877 q selected
    | true =>
      simp only [d315002, d316123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32879 q selected
  have h2 (q : Pattern) (selected : d315056 q = 0) : d316128 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315056, d316128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32885 q selected
    | true =>
      simp only [d315056, d316128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32886 q selected
  have h3 (q : Pattern) (selected : d315057 q = 0) : d316129 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315057, d316129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315057, d316129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315082 q = 0) : d316154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315082, d316154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32890 q selected
    | true =>
      simp only [d315082, d316154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315083 q = 0) : d316155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315083, d316155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315083, d316155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315084 q = 0) : d316156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315084, d316156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315084, d316156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d315085 q = 0) : d316157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315085, d316157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315085, d316157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315086 q = 0) : d316158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315086, d316158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315086, d316158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d315087 q = 0) : d316159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315087, d316159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315087, d316159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32892 (p : Pattern) (selected : d315092 p = 0) : d316127 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314996 q = 0) : d316117 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314996, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32878 q selected
    | true =>
      simp only [d314996, d316117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314997 q = 0) : d316118 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314997, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314997, d316118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315089 q = 0) : d316124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315089, d316124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315089, d316124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315090 q = 0) : d316125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315090, d316125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315090, d316125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315091 q = 0) : d316126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315091, d316126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315091, d316126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315092 q = 0) : d316127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315092, d316127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315092, d316127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32893 (p : Pattern) (selected : d315098 p = 0) : d316166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315093 q = 0) : d316161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315093, d316161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32892 q selected
    | true =>
      simp only [d315093, d316161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315094 q = 0) : d316162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315094, d316162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315094, d316162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315095 q = 0) : d316163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315095, d316163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315095, d316163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315096 q = 0) : d316164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315096, d316164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315096, d316164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d315097 q = 0) : d316165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315097, d316165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315097, d316165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315098 q = 0) : d316166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315098, d316166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315098, d316166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32894 (p : Pattern) (selected : d315104 p = 0) : d316172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314730 q = 0) : d315925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314730, d315925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314730, d315925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32826 q selected
  have h2 (q : Pattern) (selected : d314731 q = 0) : d315926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314731, d315926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314731, d315926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314740 q = 0) : d315935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314740, d315935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32826 q selected
    | true =>
      simp only [d314740, d315935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32829 q selected
  have h4 (q : Pattern) (selected : d314741 q = 0) : d315936 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314741, d315936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314741, d315936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314742 q = 0) : d315937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314742, d315937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314742, d315937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314909 q = 0) : d316030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314909, d316030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32856 q selected
    | true =>
      simp only [d314909, d316030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32865 q selected
  have h7 (q : Pattern) (selected : d314922 q = 0) : d316043 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314922, d316043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32866 q selected
    | true =>
      simp only [d314922, d316043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32867 q selected
  have h8 (q : Pattern) (selected : d314923 q = 0) : d316044 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314923, d316044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314923, d316044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314924 q = 0) : d316045 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314924, d316045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314924, d316045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314925 q = 0) : d316046 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314925, d316046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314925, d316046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314929 q = 0) : d316050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314929, d316050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314929, d316050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32868 q selected
  have h12 (q : Pattern) (selected : d314931 q = 0) : d316052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314931, d316052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314931, d316052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32869 q selected
  have h13 (q : Pattern) (selected : d314932 q = 0) : d316053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314932, d316053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314932, d316053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314933 q = 0) : d316054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314933, d316054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314933, d316054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314934 q = 0) : d316055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314934, d316055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314934, d316055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314935 q = 0) : d316056 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314935, d316056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314935, d316056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d315088 q = 0) : d316160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315088, d316160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315088, d316160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32891 q selected
  have h18 (q : Pattern) (selected : d315099 q = 0) : d316167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315099, d316167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315099, d316167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32893 q selected
  have h19 (q : Pattern) (selected : d315100 q = 0) : d316168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315100, d316168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d315100, d316168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d315101 q = 0) : d316169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315101, d316169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d315101, d316169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d315102 q = 0) : d316170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315102, d316170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d315102, d316170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d315103 q = 0) : d316171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315103, d316171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d315103, d316171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d315104 q = 0) : d316172 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315104, d316172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d315104, d316172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro32895 (p : Pattern) (selected : d315110 p = 0) : d316178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315105 q = 0) : d316173 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315105, d316173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315105, d316173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32894 q selected
  have h2 (q : Pattern) (selected : d315106 q = 0) : d316174 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315106, d316174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315106, d316174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315107 q = 0) : d316175 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315107, d316175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315107, d316175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315108 q = 0) : d316176 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315108, d316176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315108, d316176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d315109 q = 0) : d316177 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315109, d316177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315109, d316177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315110 q = 0) : d316178 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315110, d316178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315110, d316178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32896 (p : Pattern) (selected : d315116 p = 0) : d316184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d314142 q = 0) : d315486 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d314142, d315486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314142, d315486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32727 q selected
  have h2 (q : Pattern) (selected : d314143 q = 0) : d315487 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d314143, d315487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314143, d315487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314144 q = 0) : d315488 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d314144, d315488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314144, d315488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314650 q = 0) : d315845 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d314650, d315845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314650, d315845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32813 q selected
  have h5 (q : Pattern) (selected : d314651 q = 0) : d315846 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d314651, d315846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314651, d315846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314652 q = 0) : d315847 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d314652, d315847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314652, d315847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314653 q = 0) : d315848 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d314653, d315848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314653, d315848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315111 q = 0) : d316179 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315111, d316179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315111, d316179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32895 q selected
  have h9 (q : Pattern) (selected : d315112 q = 0) : d316180 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315112, d316180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315112, d316180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d315113 q = 0) : d316181 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315113, d316181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315113, d316181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d315114 q = 0) : d316182 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d315114, d316182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315114, d316182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d315115 q = 0) : d316183 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d315115, d316183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315115, d316183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315116 q = 0) : d316184 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d315116, d316184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315116, d316184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32897 (p : Pattern) (selected : d315122 p = 0) : d316190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315117 q = 0) : d316185 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d315117, d316185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32896 q selected
    | true =>
      simp only [d315117, d316185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315118 q = 0) : d316186 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d315118, d316186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315118, d316186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315119 q = 0) : d316187 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d315119, d316187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315119, d316187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315120 q = 0) : d316188 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d315120, d316188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315120, d316188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315121 q = 0) : d316189 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d315121, d316189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315121, d316189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315122 q = 0) : d316190 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d315122, d316190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315122, d316190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32898 (p : Pattern) (selected : d315128 p = 0) : d316196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315123 q = 0) : d316191 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d315123, d316191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32897 q selected
    | true =>
      simp only [d315123, d316191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315124 q = 0) : d316192 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d315124, d316192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315124, d316192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315125 q = 0) : d316193 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d315125, d316193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315125, d316193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315126 q = 0) : d316194 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d315126, d316194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315126, d316194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315127 q = 0) : d316195 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d315127, d316195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315127, d316195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315128 q = 0) : d316196 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d315128, d316196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315128, d316196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32899 (p : Pattern) (selected : d315134 p = 0) : d316202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315129 q = 0) : d316197 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d315129, d316197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32898 q selected
    | true =>
      simp only [d315129, d316197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315130 q = 0) : d316198 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d315130, d316198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315130, d316198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315131 q = 0) : d316199 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d315131, d316199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315131, d316199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315132 q = 0) : d316200 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d315132, d316200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315132, d316200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315133 q = 0) : d316201 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d315133, d316201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315133, d316201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315134 q = 0) : d316202 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d315134, d316202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315134, d316202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32900 (p : Pattern) (selected : d315140 p = 0) : d316208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315135 q = 0) : d316203 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d315135, d316203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32899 q selected
    | true =>
      simp only [d315135, d316203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315136 q = 0) : d316204 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d315136, d316204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315136, d316204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315137 q = 0) : d316205 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d315137, d316205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315137, d316205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315138 q = 0) : d316206 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d315138, d316206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315138, d316206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315139 q = 0) : d316207 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d315139, d316207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315139, d316207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315140 q = 0) : d316208 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d315140, d316208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315140, d316208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32901 (p : Pattern) (selected : d315146 p = 0) : d316214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315141 q = 0) : d316209 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d315141, d316209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32900 q selected
    | true =>
      simp only [d315141, d316209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315142 q = 0) : d316210 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d315142, d316210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315142, d316210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315143 q = 0) : d316211 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d315143, d316211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315143, d316211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315144 q = 0) : d316212 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d315144, d316212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315144, d316212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315145 q = 0) : d316213 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d315145, d316213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315145, d316213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315146 q = 0) : d316214 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d315146, d316214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315146, d316214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32902 (p : Pattern) (selected : d315152 p = 0) : d316220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315147 q = 0) : d316215 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d315147, d316215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32901 q selected
    | true =>
      simp only [d315147, d316215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315148 q = 0) : d316216 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d315148, d316216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315148, d316216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315149 q = 0) : d316217 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d315149, d316217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315149, d316217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315150 q = 0) : d316218 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d315150, d316218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315150, d316218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315151 q = 0) : d316219 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d315151, d316219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315151, d316219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315152 q = 0) : d316220 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d315152, d316220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315152, d316220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32903 (p : Pattern) (selected : d315158 p = 0) : d316226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d315153 q = 0) : d316221 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d315153, d316221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32902 q selected
    | true =>
      simp only [d315153, d316221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315154 q = 0) : d316222 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d315154, d316222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315154, d316222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315155 q = 0) : d316223 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d315155, d316223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315155, d316223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315156 q = 0) : d316224 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d315156, d316224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315156, d316224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315157 q = 0) : d316225 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d315157, d316225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315157, d316225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315158 q = 0) : d316226 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d315158, d316226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315158, d316226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32904 (p : Pattern) (selected : d313810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313807 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313808 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313809 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313810 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32905 (p : Pattern) (selected : d313818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313807 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313808 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313809 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313815 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313816 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313817 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313818 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32906 (p : Pattern) (selected : d313824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313815 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313816 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313817 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313824 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32907 (p : Pattern) (selected : d313833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313815 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313816 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313817 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313833 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32908 (p : Pattern) (selected : d313839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313811 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32904 q selected
    | true =>
      simp only [d313811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313813 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313814 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32905 q selected
    | true =>
      simp only [d313819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313821 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313822 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313823 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32906 q selected
    | true =>
      simp only [d313825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d313826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d313826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d313827 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d313828 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d313828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d313834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
    | true =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d313835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d313836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d313837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d313837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d313838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d313838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d313839 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d313839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32909 (p : Pattern) (selected : d313843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313807 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313808 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313809 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313840 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d313841 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313842 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313843 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32910 (p : Pattern) (selected : d313848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313806 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
    | true =>
      simp only [d313806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313840 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313841 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313842 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313848 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32911 (p : Pattern) (selected : d313855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32909 q selected
    | true =>
      simp only [d313844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313845 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313846 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313847 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313849 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
    | true =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313850 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313851 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313852 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313853 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
    | true =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d313835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d313836 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d313837 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d313837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d313854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d313854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d313855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d313855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32912 (p : Pattern) (selected : d313860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313829 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
    | true =>
      simp only [d313829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313830 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313831 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313832 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313860 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d313860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro32913 (p : Pattern) (selected : d313866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313849 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
    | true =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313850 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d313851 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313852 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313859 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32912 q selected
    | true =>
      simp only [d313861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313863 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d313863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d313864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d313864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d313864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d313865 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d313865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d313866 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d313866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32914 (p : Pattern) (selected : d313873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d313856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32908 q selected
    | true =>
      simp only [d313856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32911 q selected
  have h2 (q : Pattern) (selected : d313857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d313857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d313858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d313867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32911 q selected
    | true =>
      simp only [d313867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32913 q selected
  have h5 (q : Pattern) (selected : d313868 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d313868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313869 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d313869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d313870 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d313870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313871 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d313871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313872 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d313872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313873 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d313873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32915 (p : Pattern) (selected : d313877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313867 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d313867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32911 q selected
    | true =>
      simp only [d313867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32913 q selected
  have h2 (q : Pattern) (selected : d313868 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d313868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313869 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d313869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313871 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d313871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313876 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d313876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313877 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d313877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32916 (p : Pattern) (selected : d313883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32914 q selected
    | true =>
      simp only [d313874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313878 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32915 q selected
    | true =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313879 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d313880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d313880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d313881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d313882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d313883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32917 (p : Pattern) (selected : d313887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313878 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32915 q selected
    | true =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313879 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313884 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d313884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d313885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d313886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d313887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32918 (p : Pattern) (selected : d313908 p = 1) : d318553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313776 q = 1) : d313776 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d313785 q = 1) : d313785 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d313805 q = 1) : d313805 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d313888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d313888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32916 q selected
    | true =>
      simp only [d313888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32917 q selected
  have h5 (q : Pattern) (selected : d313889 q = 1) : d318549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d313889, d318549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313889, d318549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313904 q = 1) : d313904 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d313905 q = 1) : d318550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d313905, d318550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313905, d318550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313906 q = 1) : d318551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d313906, d318551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313906, d318551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d313907 q = 1) : d318552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d313907, d318552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313907, d318552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313908 q = 1) : d318553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d313908, d318553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313908, d318553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32919 (p : Pattern) (selected : d313922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313874 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32914 q selected
    | true =>
      simp only [d313874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313875 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313878 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32915 q selected
    | true =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313879 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d313880 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d313880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d313881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d313882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d313882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d313922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d313922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32920 (p : Pattern) (selected : d313923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313878 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32915 q selected
    | true =>
      simp only [d313878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d313879 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d313884 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d313884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d313885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d313886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d313886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d313923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d313923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d313923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32921 (p : Pattern) (selected : d313932 p = 1) : d318558 p = 1 := by
  have h0 (q : Pattern) (selected : d313776 q = 1) : d313776 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313785 q = 1) : d313785 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d313805 q = 1) : d313805 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d313888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d313888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32916 q selected
    | true =>
      simp only [d313888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32917 q selected
  have h4 (q : Pattern) (selected : d313889 q = 1) : d318549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d313889, d318549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313889, d318549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d313904 q = 1) : d313904 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d313905 q = 1) : d318550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d313905, d318550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313905, d318550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d313906 q = 1) : d318551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d313906, d318551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313906, d318551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313907 q = 1) : d318552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d313907, d318552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313907, d318552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d313914 q = 1) : d313914 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d313919 q = 1) : d313919 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d313921 q = 1) : d313921 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d313924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d313924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32919 q selected
    | true =>
      simp only [d313924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32920 q selected
  have h13 (q : Pattern) (selected : d313925 q = 1) : d318554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d313925, d318554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d313925, d318554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d313928 q = 1) : d313928 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d313929 q = 1) : d318555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d313929, d318555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d313929, d318555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d313930 q = 1) : d318556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d313930, d318556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d313930, d318556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d313931 q = 1) : d318557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d313931, d318557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313931, d318557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d313932 q = 1) : d318558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d313932, d318558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d313932, d318558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro32922 (p : Pattern) (selected : d313952 p = 1) : d318565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313921 q = 1) : d313921 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d313924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d313924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32919 q selected
    | true =>
      simp only [d313924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32920 q selected
  have h3 (q : Pattern) (selected : d313925 q = 1) : d318554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d313925, d318554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313925, d318554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313928 q = 1) : d313928 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d313929 q = 1) : d318555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d313929, d318555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313929, d318555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313950 q = 1) : d318563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d313950, d318563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313950, d318563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d313951 q = 1) : d318564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d313951, d318564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313951, d318564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d313952 q = 1) : d318565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d313952, d318565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313952, d318565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32923 (p : Pattern) (selected : d314055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314037 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32904 q selected
  have h2 (q : Pattern) (selected : d313811 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32904 q selected
    | true =>
      simp only [d313811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314038 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314039 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314041 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32905 q selected
  have h8 (q : Pattern) (selected : d313819 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32905 q selected
    | true =>
      simp only [d313819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314042 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313820 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d313820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314043 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314044 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314046 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32906 q selected
  have h15 (q : Pattern) (selected : d313825 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32906 q selected
    | true =>
      simp only [d313825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314047 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d313826 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d313826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314048 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314049 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314050 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
  have h21 (q : Pattern) (selected : d313834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
    | true =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d314051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d314051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d313835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d314052 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d314053 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d314053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d314054 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d314055 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro32924 (p : Pattern) (selected : d314066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314056 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32909 q selected
  have h2 (q : Pattern) (selected : d313844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32909 q selected
    | true =>
      simp only [d313844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314057 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313845 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314058 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314059 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314060 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
  have h8 (q : Pattern) (selected : d313849 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
    | true =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314061 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313850 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314062 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314063 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314064 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314050 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
  have h15 (q : Pattern) (selected : d313834 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32907 q selected
    | true =>
      simp only [d313834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d313835 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d313835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314052 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314053 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314065 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32925 (p : Pattern) (selected : d314076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314060 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
  have h2 (q : Pattern) (selected : d313849 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32910 q selected
    | true =>
      simp only [d313849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314061 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d313850 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d313850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314062 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314063 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314070 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314071 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32912 q selected
  have h9 (q : Pattern) (selected : d313861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d313861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32912 q selected
    | true =>
      simp only [d313861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314072 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d313862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d313862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314073 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314074 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314076 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32926 (p : Pattern) (selected : d314083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32923 q selected
    | true =>
      simp only [d314067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32924 q selected
  have h2 (q : Pattern) (selected : d314068 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314069 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32924 q selected
    | true =>
      simp only [d314077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32925 q selected
  have h5 (q : Pattern) (selected : d314078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314080 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314081 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314082 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314083 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32927 (p : Pattern) (selected : d314087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32924 q selected
    | true =>
      simp only [d314077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32925 q selected
  have h2 (q : Pattern) (selected : d314078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314081 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314086 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314087 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32928 (p : Pattern) (selected : d314093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314084 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32926 q selected
    | true =>
      simp only [d314084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314085 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32927 q selected
    | true =>
      simp only [d314088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32929 (p : Pattern) (selected : d314097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32927 q selected
    | true =>
      simp only [d314088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314094 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32930 (p : Pattern) (selected : d314118 p = 1) : d318575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314036 q = 1) : d314036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32928 q selected
    | true =>
      simp only [d314098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32929 q selected
  have h3 (q : Pattern) (selected : d314099 q = 1) : d318571 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314099, d318571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314099, d318571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314114 q = 1) : d314114 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314115 q = 1) : d318572 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314115, d318572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314115, d318572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314116 q = 1) : d318573 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314116, d318573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314116, d318573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314117 q = 1) : d318574 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314117, d318574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314117, d318574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314118 q = 1) : d318575 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314118, d318575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314118, d318575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32931 (p : Pattern) (selected : d314135 p = 1) : d318581 p = 1 := by
  have h0 (q : Pattern) (selected : d313768 q = 1) : d313768 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d313933 q = 1) : d318559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d313933, d318559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32918 q selected
    | true =>
      simp only [d313933, d318559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32921 q selected
  have h2 (q : Pattern) (selected : d313946 q = 1) : d313946 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d313947 q = 1) : d318560 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d313947, d318560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d313947, d318560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d313948 q = 1) : d318561 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d313948, d318561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d313948, d318561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d313949 q = 1) : d318562 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d313949, d318562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d313949, d318562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d313953 q = 1) : d318566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d313953, d318566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d313953, d318566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32922 q selected
  have h8 (q : Pattern) (selected : d313955 q = 1) : d313955 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d313956 q = 1) : d318567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d313956, d318567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d313956, d318567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d313957 q = 1) : d318568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d313957, d318568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d313957, d318568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d313958 q = 1) : d318569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d313958, d318569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d313958, d318569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d313959 q = 1) : d318570 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d313959, d318570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d313959, d318570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314119 q = 1) : d318576 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314119, d318576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314119, d318576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32930 q selected
  have h14 (q : Pattern) (selected : d314130 q = 1) : d314130 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d314131 q = 1) : d318577 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314131, d318577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314131, d318577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314132 q = 1) : d318578 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314132, d318578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314132, d318578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d314133 q = 1) : d318579 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314133, d318579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314133, d318579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d314134 q = 1) : d318580 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314134, d318580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d314134, d318580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d314135 q = 1) : d318581 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d314135, d318581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314135, d318581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32932 (p : Pattern) (selected : d314141 p = 1) : d318587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314136 q = 1) : d318582 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d314136, d318582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314136, d318582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32931 q selected
  have h2 (q : Pattern) (selected : d314137 q = 1) : d318583 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d314137, d318583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314137, d318583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314138 q = 1) : d318584 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d314138, d318584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314138, d318584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314139 q = 1) : d318585 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d314139, d318585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314139, d318585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314140 q = 1) : d318586 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d314140, d318586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314140, d318586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314141 q = 1) : d318587 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d314141, d318587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314141, d318587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32933 (p : Pattern) (selected : d314289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
    | true =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314289 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32934 (p : Pattern) (selected : d314298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
    | true =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19758 q selected
    | true =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h6 (q : Pattern) (selected : d314295 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314296 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314297 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314298 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32935 (p : Pattern) (selected : d314304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19758 q selected
    | true =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h2 (q : Pattern) (selected : d314295 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314296 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314297 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314304 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32936 (p : Pattern) (selected : d314313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19758 q selected
    | true =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314295 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314296 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314297 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19761 q selected
    | true =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h6 (q : Pattern) (selected : d314310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314313 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32937 (p : Pattern) (selected : d314319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32933 q selected
    | true =>
      simp only [d314290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32934 q selected
    | true =>
      simp only [d314299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314300 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314301 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314302 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314303 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314305 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32935 q selected
    | true =>
      simp only [d314305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314306 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314307 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
    | true =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314318 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314319 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32938 (p : Pattern) (selected : d314324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314285 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
    | true =>
      simp only [d314285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314286 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314287 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314288 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19758 q selected
    | true =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h6 (q : Pattern) (selected : d314320 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
    | true =>
      simp only [d314320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314321 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314322 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314323 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314324 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32939 (p : Pattern) (selected : d314329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19758 q selected
    | true =>
      simp only [d314294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19728 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314320 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19764 q selected
    | true =>
      simp only [d314320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314321 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314322 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314323 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19761 q selected
    | true =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h7 (q : Pattern) (selected : d314310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d314329 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32940 (p : Pattern) (selected : d314336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314325 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32938 q selected
    | true =>
      simp only [d314325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314326 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314327 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314328 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314330 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
    | true =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314332 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314333 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314334 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
    | true =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314336 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32941 (p : Pattern) (selected : d314341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19761 q selected
    | true =>
      simp only [d314309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19675 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314341 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro32942 (p : Pattern) (selected : d314347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314330 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
    | true =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314332 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314333 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314340 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32941 q selected
    | true =>
      simp only [d314342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314344 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314345 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314347 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32943 (p : Pattern) (selected : d314354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32937 q selected
    | true =>
      simp only [d314337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32940 q selected
  have h2 (q : Pattern) (selected : d314338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32940 q selected
    | true =>
      simp only [d314348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32942 q selected
  have h5 (q : Pattern) (selected : d314349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314353 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314354 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32944 (p : Pattern) (selected : d314358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32940 q selected
    | true =>
      simp only [d314348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32942 q selected
  have h2 (q : Pattern) (selected : d314349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32945 (p : Pattern) (selected : d314364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314355 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32943 q selected
    | true =>
      simp only [d314355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314356 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32944 q selected
    | true =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314364 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32946 (p : Pattern) (selected : d314368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32944 q selected
    | true =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32947 (p : Pattern) (selected : d314405 p = 1) : d318595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314255 q = 1) : d314255 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314264 q = 1) : d314264 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314284 q = 1) : d314284 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d314369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32945 q selected
    | true =>
      simp only [d314369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32946 q selected
  have h5 (q : Pattern) (selected : d314370 q = 1) : d318591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314370, d318591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314370, d318591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314401 q = 1) : d314401 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d314402 q = 1) : d318592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314402, d318592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314402, d318592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314403 q = 1) : d318593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314403, d318593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314403, d318593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314404 q = 1) : d318594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314404, d318594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314404, d318594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314405 q = 1) : d318595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314405, d318595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314405, d318595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32948 (p : Pattern) (selected : d314419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314355 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32943 q selected
    | true =>
      simp only [d314355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314356 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32944 q selected
    | true =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32949 (p : Pattern) (selected : d314420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32944 q selected
    | true =>
      simp only [d314359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314420 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32950 (p : Pattern) (selected : d314429 p = 1) : d318600 p = 1 := by
  have h0 (q : Pattern) (selected : d314255 q = 1) : d314255 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314264 q = 1) : d314264 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314284 q = 1) : d314284 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32945 q selected
    | true =>
      simp only [d314369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32946 q selected
  have h4 (q : Pattern) (selected : d314370 q = 1) : d318591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314370, d318591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314370, d318591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314401 q = 1) : d314401 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d314402 q = 1) : d318592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314402, d318592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314402, d318592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314403 q = 1) : d318593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314403, d318593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314403, d318593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314404 q = 1) : d318594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314404, d318594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314404, d318594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314411 q = 1) : d314411 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d314416 q = 1) : d314416 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d314418 q = 1) : d314418 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d314421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32948 q selected
    | true =>
      simp only [d314421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32949 q selected
  have h13 (q : Pattern) (selected : d314422 q = 1) : d318596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314422, d318596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314422, d318596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314425 q = 1) : d314425 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d314426 q = 1) : d318597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314426, d318597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314426, d318597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314427 q = 1) : d318598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314427, d318598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314427, d318598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314428 q = 1) : d318599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314428, d318599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314428, d318599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d314429 q = 1) : d318600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314429, d318600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314429, d318600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro32951 (p : Pattern) (selected : d314449 p = 1) : d318607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314418 q = 1) : d314418 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314421 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32948 q selected
    | true =>
      simp only [d314421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32949 q selected
  have h3 (q : Pattern) (selected : d314422 q = 1) : d318596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314422, d318596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314422, d318596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314425 q = 1) : d314425 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314426 q = 1) : d318597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314426, d318597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314426, d318597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314447 q = 1) : d318605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314447, d318605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314447, d318605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314448 q = 1) : d318606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314448, d318606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314448, d318606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314449 q = 1) : d318607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314449, d318607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314449, d318607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32952 (p : Pattern) (selected : d314552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314534 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32933 q selected
  have h2 (q : Pattern) (selected : d314290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32933 q selected
    | true =>
      simp only [d314290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314535 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314536 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314537 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314538 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32934 q selected
  have h8 (q : Pattern) (selected : d314299 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32934 q selected
    | true =>
      simp only [d314299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314539 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314300 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314540 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314541 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314542 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314543 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32935 q selected
  have h15 (q : Pattern) (selected : d314305 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32935 q selected
    | true =>
      simp only [d314305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314544 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314306 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314545 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314546 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314547 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
  have h21 (q : Pattern) (selected : d314314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
    | true =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d314548 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d314548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d314315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d314549 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d314549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d314550 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d314550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d314551 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d314552 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro32953 (p : Pattern) (selected : d314563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32938 q selected
  have h2 (q : Pattern) (selected : d314325 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32938 q selected
    | true =>
      simp only [d314325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314326 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314555 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314556 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
  have h8 (q : Pattern) (selected : d314330 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
    | true =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314559 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d314560 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d314561 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314547 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
  have h15 (q : Pattern) (selected : d314314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32936 q selected
    | true =>
      simp only [d314314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d314548 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d314548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d314549 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d314550 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d314550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d314562 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d314562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d314563 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32954 (p : Pattern) (selected : d314573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
  have h2 (q : Pattern) (selected : d314330 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32939 q selected
    | true =>
      simp only [d314330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314331 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314559 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314560 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314567 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314568 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32941 q selected
  have h9 (q : Pattern) (selected : d314342 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32941 q selected
    | true =>
      simp only [d314342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314569 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314343 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314572 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314573 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32955 (p : Pattern) (selected : d314580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314564 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32952 q selected
    | true =>
      simp only [d314564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32953 q selected
  have h2 (q : Pattern) (selected : d314565 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314566 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32953 q selected
    | true =>
      simp only [d314574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32954 q selected
  have h5 (q : Pattern) (selected : d314575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314578 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314579 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32956 (p : Pattern) (selected : d314584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314574 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32953 q selected
    | true =>
      simp only [d314574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32954 q selected
  have h2 (q : Pattern) (selected : d314575 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314576 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314578 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314583 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314584 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32957 (p : Pattern) (selected : d314590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314581 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32955 q selected
    | true =>
      simp only [d314581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314582 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32956 q selected
    | true =>
      simp only [d314585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314587 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314588 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32958 (p : Pattern) (selected : d314594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32956 q selected
    | true =>
      simp only [d314585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32959 (p : Pattern) (selected : d314626 p = 1) : d318617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314533 q = 1) : d314533 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32957 q selected
    | true =>
      simp only [d314595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32958 q selected
  have h3 (q : Pattern) (selected : d314596 q = 1) : d318613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314596, d318613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314596, d318613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314622 q = 1) : d314622 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314623 q = 1) : d318614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314623, d318614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314623, d318614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314624 q = 1) : d318615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314624, d318615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314624, d318615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314625 q = 1) : d318616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314625, d318616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314625, d318616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314626 q = 1) : d318617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314626, d318617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314626, d318617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32960 (p : Pattern) (selected : d314643 p = 1) : d318623 p = 1 := by
  have h0 (q : Pattern) (selected : d314247 q = 1) : d314247 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314430 q = 1) : d318601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314430, d318601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32947 q selected
    | true =>
      simp only [d314430, d318601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32950 q selected
  have h2 (q : Pattern) (selected : d314443 q = 1) : d314443 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314444 q = 1) : d318602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314444, d318602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314444, d318602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314445 q = 1) : d318603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314445, d318603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314445, d318603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314446 q = 1) : d318604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314446, d318604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314446, d318604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314450 q = 1) : d318608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314450, d318608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314450, d318608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32951 q selected
  have h8 (q : Pattern) (selected : d314452 q = 1) : d314452 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d314453 q = 1) : d318609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314453, d318609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314453, d318609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314454 q = 1) : d318610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314454, d318610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314454, d318610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d314455 q = 1) : d318611 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314455, d318611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314455, d318611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d314456 q = 1) : d318612 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314456, d318612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314456, d318612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314627 q = 1) : d318618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314627, d318618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314627, d318618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32959 q selected
  have h14 (q : Pattern) (selected : d314638 q = 1) : d314638 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d314639 q = 1) : d318619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314639, d318619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314639, d318619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314640 q = 1) : d318620 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314640, d318620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314640, d318620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d314641 q = 1) : d318621 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314641, d318621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d314641, d318621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d314642 q = 1) : d318622 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314642, d318622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d314642, d318622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d314643 q = 1) : d318623 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d314643, d318623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314643, d318623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32961 (p : Pattern) (selected : d314649 p = 1) : d318629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314644 q = 1) : d318624 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d314644, d318624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314644, d318624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32960 q selected
  have h2 (q : Pattern) (selected : d314645 q = 1) : d318625 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d314645, d318625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314645, d318625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314646 q = 1) : d318626 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d314646, d318626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314646, d318626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314647 q = 1) : d318627 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d314647, d318627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314647, d318627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314648 q = 1) : d318628 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d314648, d318628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314648, d318628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314649 q = 1) : d318629 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d314649, d318629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314649, d318629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32962 (p : Pattern) (selected : d314782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19789 q selected
    | true =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h2 (q : Pattern) (selected : d314779 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314780 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314781 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314782 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro32963 (p : Pattern) (selected : d314792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19789 q selected
    | true =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314779 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314780 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314781 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314788 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19793 q selected
    | true =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19794 q selected
  have h6 (q : Pattern) (selected : d314789 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d314790 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314791 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314792 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro32964 (p : Pattern) (selected : d314798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32962 q selected
    | true =>
      simp only [d314783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314785 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314786 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314787 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
    | true =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314795 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314796 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314797 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314798 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32965 (p : Pattern) (selected : d314803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19789 q selected
    | true =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h2 (q : Pattern) (selected : d314799 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
    | true =>
      simp only [d314799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314800 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314803 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32966 (p : Pattern) (selected : d314808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314778 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19789 q selected
    | true =>
      simp only [d314778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19790 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314799 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19798 q selected
    | true =>
      simp only [d314799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314800 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314801 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314802 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d314788 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19793 q selected
    | true =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19794 q selected
  have h7 (q : Pattern) (selected : d314789 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d314790 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d314791 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d314808 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32967 (p : Pattern) (selected : d314815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314804 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32965 q selected
    | true =>
      simp only [d314804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314805 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314806 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314807 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
    | true =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314813 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
    | true =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d314795 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d314796 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d314796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d314814 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d314815 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32968 (p : Pattern) (selected : d314820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d314788 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19793 q selected
    | true =>
      simp only [d314788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19794 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314789 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314790 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d314791 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d314820 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d314820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro32969 (p : Pattern) (selected : d314826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
    | true =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d314811 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314812 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314819 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314821 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32968 q selected
    | true =>
      simp only [d314821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314822 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314823 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d314823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314824 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d314824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314825 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d314825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d314826 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d314826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32970 (p : Pattern) (selected : d314833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314816 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32964 q selected
    | true =>
      simp only [d314816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32967 q selected
  have h2 (q : Pattern) (selected : d314817 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314818 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314827 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32967 q selected
    | true =>
      simp only [d314827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32969 q selected
  have h5 (q : Pattern) (selected : d314828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314830 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314831 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d314832 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314833 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32971 (p : Pattern) (selected : d314837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314827 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d314827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32967 q selected
    | true =>
      simp only [d314827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32969 q selected
  have h2 (q : Pattern) (selected : d314828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d314828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d314829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314831 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d314831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314836 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d314836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314837 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d314837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32972 (p : Pattern) (selected : d314843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32970 q selected
    | true =>
      simp only [d314834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32971 q selected
    | true =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314843 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32973 (p : Pattern) (selected : d314847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32971 q selected
    | true =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32974 (p : Pattern) (selected : d314884 p = 1) : d318638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314750 q = 1) : d314750 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314759 q = 1) : d314759 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314777 q = 1) : d314777 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d314848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32972 q selected
    | true =>
      simp only [d314848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32973 q selected
  have h5 (q : Pattern) (selected : d314849 q = 1) : d318634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314849, d318634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314849, d318634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314880 q = 1) : d314880 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d314881 q = 1) : d318635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314881, d318635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314881, d318635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314882 q = 1) : d318636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314882, d318636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314882, d318636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314883 q = 1) : d318637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314883, d318637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314883, d318637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314884 q = 1) : d318638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314884, d318638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314884, d318638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro32975 (p : Pattern) (selected : d314898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32970 q selected
    | true =>
      simp only [d314834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32971 q selected
    | true =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d314842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d314898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32976 (p : Pattern) (selected : d314899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32971 q selected
    | true =>
      simp only [d314838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d314844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d314845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d314845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d314846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d314899 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d314899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d314899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32977 (p : Pattern) (selected : d314908 p = 1) : d318643 p = 1 := by
  have h0 (q : Pattern) (selected : d314750 q = 1) : d314750 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314759 q = 1) : d314759 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314777 q = 1) : d314777 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32972 q selected
    | true =>
      simp only [d314848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32973 q selected
  have h4 (q : Pattern) (selected : d314849 q = 1) : d318634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314849, d318634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314849, d318634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d314880 q = 1) : d314880 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d314881 q = 1) : d318635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314881, d318635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314881, d318635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314882 q = 1) : d318636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314882, d318636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314882, d318636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314883 q = 1) : d318637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314883, d318637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314883, d318637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d314890 q = 1) : d314890 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d314895 q = 1) : d314895 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d314897 q = 1) : d314897 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d314900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32975 q selected
    | true =>
      simp only [d314900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32976 q selected
  have h13 (q : Pattern) (selected : d314901 q = 1) : d318639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314901, d318639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d314901, d318639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d314904 q = 1) : d314904 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d314905 q = 1) : d318640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314905, d318640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d314905, d318640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d314906 q = 1) : d318641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314906, d318641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314906, d318641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314907 q = 1) : d318642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314907, d318642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314907, d318642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d314908 q = 1) : d318643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314908, d318643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314908, d318643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro32978 (p : Pattern) (selected : d314928 p = 1) : d318650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314897 q = 1) : d314897 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d314900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d314900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32975 q selected
    | true =>
      simp only [d314900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32976 q selected
  have h3 (q : Pattern) (selected : d314901 q = 1) : d318639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d314901, d318639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314901, d318639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314904 q = 1) : d314904 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314905 q = 1) : d318640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d314905, d318640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314905, d318640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314926 q = 1) : d318648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d314926, d318648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314926, d318648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314927 q = 1) : d318649 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d314927, d318649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314927, d318649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d314928 q = 1) : d318650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d314928, d318650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314928, d318650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32979 (p : Pattern) (selected : d315013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315003 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32962 q selected
  have h2 (q : Pattern) (selected : d314783 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32962 q selected
    | true =>
      simp only [d314783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315004 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314784 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315005 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315006 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315008 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
  have h9 (q : Pattern) (selected : d314793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
    | true =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d315009 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d315009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d315010 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d315010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315011 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d315012 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d315013 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32980 (p : Pattern) (selected : d315024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315014 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32965 q selected
  have h2 (q : Pattern) (selected : d314804 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32965 q selected
    | true =>
      simp only [d314804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315015 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314805 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315016 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315017 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
  have h8 (q : Pattern) (selected : d314809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
    | true =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d315019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d315020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d315020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d315021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d315021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d315022 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d315008 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
  have h15 (q : Pattern) (selected : d314793 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32963 q selected
    | true =>
      simp only [d314793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d315009 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d315009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d314794 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d314794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d315010 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d315010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d315011 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d315011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d315023 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d315023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d315024 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro32981 (p : Pattern) (selected : d315034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
  have h2 (q : Pattern) (selected : d314809 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32966 q selected
    | true =>
      simp only [d314809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314810 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d314810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315028 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315029 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32968 q selected
  have h9 (q : Pattern) (selected : d314821 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d314821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32968 q selected
    | true =>
      simp only [d314821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d315030 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d315030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d314822 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d314822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d315031 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d315031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315032 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d315033 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d315034 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro32982 (p : Pattern) (selected : d315041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315025 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32979 q selected
    | true =>
      simp only [d315025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32980 q selected
  have h2 (q : Pattern) (selected : d315026 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315027 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32980 q selected
    | true =>
      simp only [d315035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32981 q selected
  have h5 (q : Pattern) (selected : d315036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d315038 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d315040 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d315041 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d315041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro32983 (p : Pattern) (selected : d315045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315035 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32980 q selected
    | true =>
      simp only [d315035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32981 q selected
  have h2 (q : Pattern) (selected : d315036 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315037 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315044 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315045 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32984 (p : Pattern) (selected : d315051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315042 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32982 q selected
    | true =>
      simp only [d315042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315043 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32983 q selected
    | true =>
      simp only [d315046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d315048 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315049 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d315050 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d315050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d315051 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro32985 (p : Pattern) (selected : d315055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32983 q selected
    | true =>
      simp only [d315046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315053 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315054 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32986 (p : Pattern) (selected : d315087 p = 1) : d318660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315002 q = 1) : d315002 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d315056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32984 q selected
    | true =>
      simp only [d315056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32985 q selected
  have h3 (q : Pattern) (selected : d315057 q = 1) : d318656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315057, d318656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315057, d318656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315083 q = 1) : d315083 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d315084 q = 1) : d318657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315084, d318657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315084, d318657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315085 q = 1) : d318658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315085, d318658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315085, d318658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d315086 q = 1) : d318659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315086, d318659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315086, d318659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315087 q = 1) : d318660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315087, d318660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315087, d318660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro32987 (p : Pattern) (selected : d315104 p = 1) : d318666 p = 1 := by
  have h0 (q : Pattern) (selected : d314742 q = 1) : d314742 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314909 q = 1) : d318644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314909, d318644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32974 q selected
    | true =>
      simp only [d314909, d318644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32977 q selected
  have h2 (q : Pattern) (selected : d314922 q = 1) : d314922 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d314923 q = 1) : d318645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314923, d318645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314923, d318645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d314924 q = 1) : d318646 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314924, d318646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314924, d318646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314925 q = 1) : d318647 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314925, d318647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314925, d318647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314929 q = 1) : d318651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d314929, d318651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314929, d318651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32978 q selected
  have h8 (q : Pattern) (selected : d314931 q = 1) : d314931 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d314932 q = 1) : d318652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d314932, d318652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d314932, d318652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d314933 q = 1) : d318653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d314933, d318653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314933, d318653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d314934 q = 1) : d318654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d314934, d318654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d314934, d318654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d314935 q = 1) : d318655 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d314935, d318655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d314935, d318655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315088 q = 1) : d318661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315088, d318661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315088, d318661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32986 q selected
  have h14 (q : Pattern) (selected : d315099 q = 1) : d315099 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d315100 q = 1) : d318662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315100, d318662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d315100, d318662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d315101 q = 1) : d318663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315101, d318663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d315101, d318663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d315102 q = 1) : d318664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315102, d318664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d315102, d318664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d315103 q = 1) : d318665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315103, d318665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d315103, d318665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d315104 q = 1) : d318666 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315104, d318666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315104, d318666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro32988 (p : Pattern) (selected : d315110 p = 1) : d318672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315105 q = 1) : d318667 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315105, d318667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315105, d318667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32987 q selected
  have h2 (q : Pattern) (selected : d315106 q = 1) : d318668 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315106, d318668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315106, d318668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d315107 q = 1) : d318669 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315107, d318669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315107, d318669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d315108 q = 1) : d318670 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315108, d318670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315108, d318670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d315109 q = 1) : d318671 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315109, d318671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315109, d318671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d315110 q = 1) : d318672 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315110, d318672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315110, d318672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro32989 (p : Pattern) (selected : d315116 p = 1) : d318678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d314142 q = 1) : d318588 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d314142, d318588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314142, d318588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32932 q selected
  have h2 (q : Pattern) (selected : d314143 q = 1) : d318589 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d314143, d318589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314143, d318589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d314144 q = 1) : d318590 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d314144, d318590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314144, d318590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d314650 q = 1) : d318630 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d314650, d318630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314650, d318630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32961 q selected
  have h5 (q : Pattern) (selected : d314651 q = 1) : d318631 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d314651, d318631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314651, d318631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d314652 q = 1) : d318632 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d314652, d318632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d314652, d318632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d314653 q = 1) : d318633 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d314653, d318633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d314653, d318633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d315111 q = 1) : d318673 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315111, d318673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315111, d318673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32988 q selected
  have h9 (q : Pattern) (selected : d315112 q = 1) : d318674 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315112, d318674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315112, d318674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d315113 q = 1) : d318675 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315113, d318675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315113, d318675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d315114 q = 1) : d318676 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d315114, d318676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d315114, d318676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d315115 q = 1) : d318677 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d315115, d318677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d315115, d318677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d315116 q = 1) : d318678 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d315116, d318678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d315116, d318678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro32990 (p : Pattern) (selected : d315122 p = 1) : d318684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315117 q = 1) : d318679 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d315117, d318679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32989 q selected
    | true =>
      simp only [d315117, d318679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315118 q = 1) : d318680 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d315118, d318680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315118, d318680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315119 q = 1) : d318681 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d315119, d318681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315119, d318681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315120 q = 1) : d318682 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d315120, d318682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315120, d318682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315121 q = 1) : d318683 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d315121, d318683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315121, d318683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315122 q = 1) : d318684 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d315122, d318684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315122, d318684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32991 (p : Pattern) (selected : d315128 p = 1) : d318690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315123 q = 1) : d318685 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d315123, d318685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32990 q selected
    | true =>
      simp only [d315123, d318685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315124 q = 1) : d318686 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d315124, d318686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315124, d318686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315125 q = 1) : d318687 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d315125, d318687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315125, d318687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315126 q = 1) : d318688 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d315126, d318688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315126, d318688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315127 q = 1) : d318689 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d315127, d318689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315127, d318689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315128 q = 1) : d318690 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d315128, d318690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315128, d318690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32992 (p : Pattern) (selected : d315134 p = 1) : d318696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315129 q = 1) : d318691 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d315129, d318691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32991 q selected
    | true =>
      simp only [d315129, d318691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315130 q = 1) : d318692 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d315130, d318692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315130, d318692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315131 q = 1) : d318693 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d315131, d318693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315131, d318693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315132 q = 1) : d318694 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d315132, d318694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315132, d318694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315133 q = 1) : d318695 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d315133, d318695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315133, d318695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315134 q = 1) : d318696 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d315134, d318696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315134, d318696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32993 (p : Pattern) (selected : d315140 p = 1) : d318702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315135 q = 1) : d318697 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d315135, d318697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32992 q selected
    | true =>
      simp only [d315135, d318697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315136 q = 1) : d318698 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d315136, d318698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315136, d318698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315137 q = 1) : d318699 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d315137, d318699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315137, d318699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315138 q = 1) : d318700 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d315138, d318700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315138, d318700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315139 q = 1) : d318701 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d315139, d318701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315139, d318701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315140 q = 1) : d318702 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d315140, d318702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315140, d318702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32994 (p : Pattern) (selected : d315146 p = 1) : d318708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315141 q = 1) : d318703 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d315141, d318703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32993 q selected
    | true =>
      simp only [d315141, d318703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315142 q = 1) : d318704 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d315142, d318704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315142, d318704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315143 q = 1) : d318705 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d315143, d318705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315143, d318705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315144 q = 1) : d318706 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d315144, d318706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315144, d318706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315145 q = 1) : d318707 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d315145, d318707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315145, d318707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315146 q = 1) : d318708 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d315146, d318708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315146, d318708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32995 (p : Pattern) (selected : d315152 p = 1) : d318714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315147 q = 1) : d318709 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d315147, d318709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32994 q selected
    | true =>
      simp only [d315147, d318709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315148 q = 1) : d318710 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d315148, d318710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315148, d318710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315149 q = 1) : d318711 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d315149, d318711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315149, d318711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315150 q = 1) : d318712 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d315150, d318712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315150, d318712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315151 q = 1) : d318713 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d315151, d318713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315151, d318713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315152 q = 1) : d318714 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d315152, d318714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315152, d318714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32996 (p : Pattern) (selected : d315158 p = 1) : d318720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d315153 q = 1) : d318715 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d315153, d318715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32995 q selected
    | true =>
      simp only [d315153, d318715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d315154 q = 1) : d318716 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d315154, d318716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d315154, d318716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d315155 q = 1) : d318717 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d315155, d318717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d315155, d318717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d315156 q = 1) : d318718 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d315156, d318718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d315156, d318718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d315157 q = 1) : d318719 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d315157, d318719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d315157, d318719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d315158 q = 1) : d318720 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d315158, d318720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d315158, d318720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro32997 (p : Pattern) (selected : d44884 p = 0) : d318729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44880 q = 0) : d263912 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44881 q = 0) : d318726 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44881, d318726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44882 q = 0) : d318727 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44882, d318727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16 q = 0) : d51868 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44883 q = 0) : d318728 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44883, d318728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17 q = 0) : d51869 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44884 q = 0) : d318729 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44884, d318729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44884, d318729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32998 (p : Pattern) (selected : d44890 p = 0) : d318735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d44885 q = 0) : d318730 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32997 q selected
    | true =>
      simp only [d44885, d318730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44886 q = 0) : d318731 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44886, d318731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d44887 q = 0) : d318732 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44887, d318732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44888 q = 0) : d318733 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44888, d318733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44889 q = 0) : d318734 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44889, d318734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d22 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d23 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44890 q = 0) : d318735 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44890, d318735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44890, d318735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro32999 (p : Pattern) (selected : d44896 p = 0) : d318741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d44891 q = 0) : d318736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32998 q selected
    | true =>
      simp only [d44891, d318736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44892 q = 0) : d318737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44892, d318737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44893 q = 0) : d318738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44893, d318738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44894 q = 0) : d318739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44894, d318739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44895 q = 0) : d318740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44895, d318740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44895, d318740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d29 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44896 q = 0) : d318741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44896, d318741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44896, d318741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
end NetHack.Soko22Hazard87
