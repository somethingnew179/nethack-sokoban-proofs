import NetHack.Soko22Hazard87.AndIntroBlocks0250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro62750 (p : Pattern) (ha : d248583 p = 1) (hb : d249697 p = 1) : d250749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248578 q = 1) (hb : d249692 q = 1) : d250744 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d248578, d249692, d250744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62749 q ha hb
    | true =>
      simp only [d248578, d249692, d250744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248579 q = 1) (hb : d249693 q = 1) : d250745 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d248579, d249693, d250745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248579, d249693, d250745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248580 q = 1) (hb : d249694 q = 1) : d250746 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d248580, d249694, d250746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248580, d249694, d250746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248581 q = 1) (hb : d249695 q = 1) : d250747 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d248581, d249695, d250747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248581, d249695, d250747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248582 q = 1) (hb : d249696 q = 1) : d250748 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d248582, d249696, d250748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248582, d249696, d250748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248583 q = 1) (hb : d249697 q = 1) : d250749 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d248583, d249697, d250749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248583, d249697, d250749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62751 (p : Pattern) (ha : d152855 p = 1) (hb : d245682 p = 1) : d156818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25130 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
    | true =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h2 (q : Pattern) (ha : d25190 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25191 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25191, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25192 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25193 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245682 q = 1) : d156818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245682, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245682, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62752 (p : Pattern) (ha : d152855 p = 1) (hb : d245692 p = 1) : d156859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25166 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62159 q ha hb
    | true =>
      simp only [d25166, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245688 q = 1) : d156855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245688, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245688, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245689 q = 1) : d156856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245689, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245689, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245690 q = 1) : d156857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245690, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245690, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245691 q = 1) : d156858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245691, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245691, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245692 q = 1) : d156859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245692, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245692, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62753 (p : Pattern) (ha : d152855 p = 1) (hb : d245698 p = 1) : d158042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d152855 q = 1) : d156625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62162 q ha hb
    | true =>
      simp only [d25195, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62163 q ha hb
  have h2 (q : Pattern) (ha : d25196 q = 1) (hb : d152855 q = 1) : d156626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245680 q = 1) : d158032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245680, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245680, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245681 q = 1) : d158033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245681, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245681, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245683 q = 1) : d156819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245683, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245683, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62751 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245684 q = 1) : d158034 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245684, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245684, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245685 q = 1) : d158035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245685, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245685, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245686 q = 1) : d158036 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245686, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245686, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245687 q = 1) : d158037 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245687, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245687, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245693 q = 1) : d156860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245693, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245693, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62752 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245694 q = 1) : d158038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245694, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245694, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245695 q = 1) : d158039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245695, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245695, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245696 q = 1) : d158040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245696, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245696, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245697 q = 1) : d158041 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245697, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245697, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245698 q = 1) : d158042 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245698, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245698, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62754 (p : Pattern) (ha : d152855 p = 1) (hb : d245704 p = 1) : d158048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30681 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245699 q = 1) : d158043 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245699, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245699, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62753 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245700 q = 1) : d158044 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245700, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245700, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245701 q = 1) : d158045 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245701, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245701, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245702 q = 1) : d158046 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245702, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245702, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245703 q = 1) : d158047 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245703, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245703, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245704 q = 1) : d158048 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245704, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245704, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62755 (p : Pattern) (ha : d152855 p = 1) (hb : d245707 p = 1) : d158051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25402 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62191 q ha hb
    | true =>
      simp only [d25402, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62192 q ha hb
  have h2 (q : Pattern) (ha : d25403 q = 1) (hb : d152855 q = 1) : d156738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25404 q = 1) (hb : d152855 q = 1) : d156739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25404, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25405 q = 1) (hb : d152855 q = 1) : d156740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25406 q = 1) (hb : d152855 q = 1) : d156741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245707 q = 1) : d158051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245707, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62756 (p : Pattern) (ha : d152855 p = 1) (hb : d245718 p = 1) : d158061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245713 q = 1) : d156713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62226 q hb ha
    | true =>
      simp only [d245713, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62198 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245714 q = 1) : d158057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245714, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245715 q = 1) : d158058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245715, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245716 q = 1) : d158059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245716, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245717 q = 1) : d158060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245717, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245718 q = 1) : d158061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245718, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62757 (p : Pattern) (ha : d152855 p = 1) (hb : d245724 p = 1) : d158067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d152855 q = 1) : d156743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62190 q ha hb
    | true =>
      simp only [d25408, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62193 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d152855 q = 1) : d156744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245705 q = 1) : d158049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245705, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245706 q = 1) : d158050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245706, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245708 q = 1) : d158052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245708, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62755 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245709 q = 1) : d158053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245710 q = 1) : d158054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245711 q = 1) : d158055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245712 q = 1) : d158056 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245719 q = 1) : d158062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245719, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62756 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245720 q = 1) : d158063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245721 q = 1) : d158064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245722 q = 1) : d158065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245723 q = 1) : d158066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245724 q = 1) : d158067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62758 (p : Pattern) (ha : d152855 p = 1) (hb : d245730 p = 1) : d158073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245725 q = 1) : d158068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245725, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62757 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245726 q = 1) : d158069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245726, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245727 q = 1) : d158070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245727, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245728 q = 1) : d158071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245728, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245729 q = 1) : d158072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245729, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245730 q = 1) : d158073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245730, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62759 (p : Pattern) (ha : d152855 p = 1) (hb : d245734 p = 1) : d250752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d152855 q = 1) : d248695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d248695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62240 q ha hb
    | true =>
      simp only [d25735, d248695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62241 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d152855 q = 1) : d248696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d248696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d248696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d152855 q = 1) : d248697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d248697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d248697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d152855 q = 1) : d248698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d248698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d248698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d152855 q = 1) : d248699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d248699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d248699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245734 q = 1) : d250752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d250752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245734, d250752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62760 (p : Pattern) (ha : d152855 p = 1) (hb : d245745 p = 1) : d250763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245740 q = 1) : d250758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d250758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62278 q hb ha
    | true =>
      simp only [d245740, d250758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62249 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245741 q = 1) : d250759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d250759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245741, d250759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245742 q = 1) : d250760 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d250760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d250760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245743 q = 1) : d250761 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d250761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245743, d250761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245744 q = 1) : d250762 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d250762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245744, d250762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245745 q = 1) : d250763 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d250763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245745, d250763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62761 (p : Pattern) (ha : d152855 p = 1) (hb : d245751 p = 1) : d250769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d152855 q = 1) : d248701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d248701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62239 q ha hb
    | true =>
      simp only [d25741, d248701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62242 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d152855 q = 1) : d248702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d248702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d248702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245732 q = 1) : d250750 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d250750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245732, d250750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245733 q = 1) : d250751 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d250751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245733, d250751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245735 q = 1) : d250753 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d250753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245735, d250753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62759 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245736 q = 1) : d250754 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d250754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d250754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245737 q = 1) : d250755 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d250755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d250755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245738 q = 1) : d250756 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d250756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d250756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245739 q = 1) : d250757 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d250757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d250757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245746 q = 1) : d250764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d250764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245746, d250764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62760 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245747 q = 1) : d250765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d250765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d250765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245748 q = 1) : d250766 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d250766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d250766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245749 q = 1) : d250767 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d250767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d250767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245750 q = 1) : d250768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d250768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d250768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245751 q = 1) : d250769 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d250769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d250769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62762 (p : Pattern) (ha : d152855 p = 1) (hb : d245757 p = 1) : d250775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245752 q = 1) : d250770 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d250770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245752, d250770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62761 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245753 q = 1) : d250771 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d250771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245753, d250771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245754 q = 1) : d250772 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d250772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245754, d250772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245755 q = 1) : d250773 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d250773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245755, d250773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245756 q = 1) : d250774 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d250774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245756, d250774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245757 q = 1) : d250775 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d250775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245757, d250775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62763 (p : Pattern) (ha : d152855 p = 1) (hb : d245762 p = 1) : d250780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d152855 q = 1) : d248908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d248908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62295 q ha hb
    | true =>
      simp only [d26159, d248908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62296 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d152855 q = 1) : d248909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d248909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d248909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d152855 q = 1) : d248910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d248910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d248910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d152855 q = 1) : d248911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d248911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d248911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d152855 q = 1) : d248912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d248912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d248912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245762 q = 1) : d250780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d250780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245762, d250780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62764 (p : Pattern) (ha : d152855 p = 1) (hb : d245773 p = 1) : d250791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245768 q = 1) : d250786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d250786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62335 q hb ha
    | true =>
      simp only [d245768, d250786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62304 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245769 q = 1) : d250787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d250787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245769, d250787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245770 q = 1) : d250788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d250788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d250788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245771 q = 1) : d250789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d250789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245771, d250789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245772 q = 1) : d250790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d250790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245772, d250790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245773 q = 1) : d250791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d250791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245773, d250791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62765 (p : Pattern) (ha : d152855 p = 1) (hb : d245779 p = 1) : d250797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d152855 q = 1) : d248914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d248914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62294 q ha hb
    | true =>
      simp only [d26165, d248914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62297 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d152855 q = 1) : d248915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d248915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d248915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245760 q = 1) : d250778 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d250778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245760, d250778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245761 q = 1) : d250779 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d250779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245761, d250779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245763 q = 1) : d250781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d250781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245763, d250781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62763 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245764 q = 1) : d250782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d250782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d250782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245765 q = 1) : d250783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d250783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d250783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245766 q = 1) : d250784 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d250784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d250784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245767 q = 1) : d250785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d250785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d250785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245774 q = 1) : d250792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d250792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245774, d250792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62764 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245775 q = 1) : d250793 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d250793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d250793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245776 q = 1) : d250794 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d250794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d250794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245777 q = 1) : d250795 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d250795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d250795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245778 q = 1) : d250796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d250796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d250796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245779 q = 1) : d250797 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d250797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d250797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62766 (p : Pattern) (ha : d152855 p = 1) (hb : d245785 p = 1) : d250803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245780 q = 1) : d250798 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d250798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245780, d250798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62765 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245781 q = 1) : d250799 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d250799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245781, d250799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245782 q = 1) : d250800 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d250800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245782, d250800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245783 q = 1) : d250801 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d250801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245783, d250801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245784 q = 1) : d250802 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d250802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245784, d250802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245785 q = 1) : d250803 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d250803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245785, d250803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62767 (p : Pattern) (ha : d152855 p = 1) (hb : d245791 p = 1) : d250809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d152855 q = 1) : d249184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d249184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62354 q ha hb
    | true =>
      simp only [d26626, d249184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62355 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d152855 q = 1) : d249185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d249185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d249185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d152855 q = 1) : d249186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d249186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d249186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d152855 q = 1) : d249187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d249187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d249187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d152855 q = 1) : d249188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d249188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d249188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245791 q = 1) : d250809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d250809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245791, d250809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62768 (p : Pattern) (ha : d152855 p = 1) (hb : d245802 p = 1) : d250820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245797 q = 1) : d250815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d250815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62394 q hb ha
    | true =>
      simp only [d245797, d250815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62363 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245798 q = 1) : d250816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d250816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245798, d250816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245799 q = 1) : d250817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d250817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d250817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245800 q = 1) : d250818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d250818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245800, d250818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245801 q = 1) : d250819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d250819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245801, d250819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245802 q = 1) : d250820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d250820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245802, d250820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62769 (p : Pattern) (ha : d152855 p = 1) (hb : d245808 p = 1) : d250826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d152855 q = 1) : d249190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d249190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62353 q ha hb
    | true =>
      simp only [d26632, d249190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62356 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d152855 q = 1) : d249191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d249191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d249191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245789 q = 1) : d250807 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d250807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245789, d250807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245790 q = 1) : d250808 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d250808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245790, d250808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245792 q = 1) : d250810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d250810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245792, d250810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62767 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245793 q = 1) : d250811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d250811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d250811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245794 q = 1) : d250812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d250812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d250812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245795 q = 1) : d250813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d250813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d250813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245796 q = 1) : d250814 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d250814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d250814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245803 q = 1) : d250821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d250821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245803, d250821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62768 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245804 q = 1) : d250822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d250822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d250822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245805 q = 1) : d250823 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d250823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d250823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245806 q = 1) : d250824 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d250824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d250824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245807 q = 1) : d250825 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d250825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d250825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245808 q = 1) : d250826 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d250826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d250826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62770 (p : Pattern) (ha : d152855 p = 1) (hb : d245814 p = 1) : d250832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245809 q = 1) : d250827 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d250827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245809, d250827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62769 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245810 q = 1) : d250828 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d250828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245810, d250828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245811 q = 1) : d250829 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d250829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245811, d250829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245812 q = 1) : d250830 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d250830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245812, d250830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245813 q = 1) : d250831 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d250831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245813, d250831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245814 q = 1) : d250832 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d250832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245814, d250832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62771 (p : Pattern) (ha : d152855 p = 1) (hb : d245821 p = 1) : d250839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d152855 q = 1) : d249455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d249455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62412 q ha hb
    | true =>
      simp only [d27079, d249455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62413 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d152855 q = 1) : d249456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d249456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d249456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d152855 q = 1) : d249457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d249457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d249457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d152855 q = 1) : d249458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d249458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d249458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d152855 q = 1) : d249459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d249459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d249459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245821 q = 1) : d250839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d250839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245821, d250839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62772 (p : Pattern) (ha : d152855 p = 1) (hb : d245832 p = 1) : d250850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245827 q = 1) : d250845 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d250845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62452 q hb ha
    | true =>
      simp only [d245827, d250845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62421 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245828 q = 1) : d250846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d250846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245828, d250846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245829 q = 1) : d250847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d250847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d250847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245830 q = 1) : d250848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d250848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245830, d250848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245831 q = 1) : d250849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d250849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245831, d250849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245832 q = 1) : d250850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d250850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245832, d250850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62773 (p : Pattern) (ha : d152855 p = 1) (hb : d245838 p = 1) : d250856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d152855 q = 1) : d249461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d249461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62411 q ha hb
    | true =>
      simp only [d27085, d249461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62414 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d152855 q = 1) : d249462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d249462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d249462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245819 q = 1) : d250837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d250837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245819, d250837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245820 q = 1) : d250838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d250838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245820, d250838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245822 q = 1) : d250840 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d250840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245822, d250840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62771 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245823 q = 1) : d250841 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d250841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d250841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245824 q = 1) : d250842 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d250842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d250842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245825 q = 1) : d250843 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d250843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d250843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245826 q = 1) : d250844 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d250844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d250844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245833 q = 1) : d250851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d250851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245833, d250851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62772 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245834 q = 1) : d250852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d250852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d250852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245835 q = 1) : d250853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d250853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d250853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245836 q = 1) : d250854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d250854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d250854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245837 q = 1) : d250855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d250855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d250855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245838 q = 1) : d250856 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d250856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d250856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62774 (p : Pattern) (ha : d152855 p = 1) (hb : d245844 p = 1) : d250862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245839 q = 1) : d250857 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d250857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245839, d250857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62773 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245840 q = 1) : d250858 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d250858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245840, d250858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245841 q = 1) : d250859 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d250859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245841, d250859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245842 q = 1) : d250860 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d250860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245842, d250860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245843 q = 1) : d250861 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d250861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245843, d250861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245844 q = 1) : d250862 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d250862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245844, d250862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62775 (p : Pattern) (ha : d152855 p = 1) (hb : d245850 p = 1) : d250868 p = 1 := by
  have h0 (q : Pattern) (ha : d152855 q = 1) (hb : d245731 q = 1) : d158074 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62754 q ha hb
    | true =>
      simp only [d245731, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62758 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245758 q = 1) : d250776 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d250776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245758, d250776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62762 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245759 q = 1) : d250777 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d250777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245759, d250777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245786 q = 1) : d250804 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d250804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245786, d250804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62766 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245787 q = 1) : d250805 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d250805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245787, d250805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245788 q = 1) : d250806 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d250806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245788, d250806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d245815 q = 1) : d250833 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d250833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245815, d250833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62770 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d245816 q = 1) : d250834 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d250834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245816, d250834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d245817 q = 1) : d250835 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d250835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245817, d250835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d245818 q = 1) : d250836 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d250836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245818, d250836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d245845 q = 1) : d250863 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d250863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245845, d250863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62774 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d245846 q = 1) : d250864 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d250864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245846, d250864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d245847 q = 1) : d250865 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d250865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245847, d250865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d245848 q = 1) : d250866 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d250866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245848, d250866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d245849 q = 1) : d250867 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d250867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245849, d250867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d245850 q = 1) : d250868 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d250868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245850, d250868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62776 (p : Pattern) (ha : d152855 p = 1) (hb : d245856 p = 1) : d250874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245851 q = 1) : d250869 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d250869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62775 q ha hb
    | true =>
      simp only [d245851, d250869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245852 q = 1) : d250870 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d250870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d250870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245853 q = 1) : d250871 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d250871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d250871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245854 q = 1) : d250872 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d250872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d250872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245855 q = 1) : d250873 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d250873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d250873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245856 q = 1) : d250874 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d250874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d250874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62777 (p : Pattern) (ha : d152855 p = 1) (hb : d245862 p = 1) : d250880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245857 q = 1) : d250875 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d250875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62776 q ha hb
    | true =>
      simp only [d245857, d250875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245858 q = 1) : d250876 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d250876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d250876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245859 q = 1) : d250877 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d250877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d250877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245860 q = 1) : d250878 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d250878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d250878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245861 q = 1) : d250879 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d250879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d250879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245862 q = 1) : d250880 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d250880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d250880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62778 (p : Pattern) (ha : d152855 p = 1) (hb : d245868 p = 1) : d250886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245863 q = 1) : d250881 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d250881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62777 q ha hb
    | true =>
      simp only [d245863, d250881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245864 q = 1) : d250882 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d250882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d250882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245865 q = 1) : d250883 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d250883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d250883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245866 q = 1) : d250884 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d250884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d250884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245867 q = 1) : d250885 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d250885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d250885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245868 q = 1) : d250886 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d250886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d250886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62779 (p : Pattern) (ha : d152855 p = 1) (hb : d245874 p = 1) : d250892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245869 q = 1) : d250887 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d250887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62778 q ha hb
    | true =>
      simp only [d245869, d250887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245870 q = 1) : d250888 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d250888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d250888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245871 q = 1) : d250889 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d250889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d250889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245872 q = 1) : d250890 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d250890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d250890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245873 q = 1) : d250891 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d250891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d250891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245874 q = 1) : d250892 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d250892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d250892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62780 (p : Pattern) (ha : d152855 p = 1) (hb : d245880 p = 1) : d250898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245875 q = 1) : d250893 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d250893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62779 q ha hb
    | true =>
      simp only [d245875, d250893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245876 q = 1) : d250894 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d250894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d250894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245877 q = 1) : d250895 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d250895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d250895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245878 q = 1) : d250896 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d250896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d250896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245879 q = 1) : d250897 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d250897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d250897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245880 q = 1) : d250898 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d250898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d250898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62781 (p : Pattern) (ha : d152855 p = 1) (hb : d245886 p = 1) : d250904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245881 q = 1) : d250899 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d250899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62780 q ha hb
    | true =>
      simp only [d245881, d250899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245882 q = 1) : d250900 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d250900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d250900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245883 q = 1) : d250901 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d250901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d250901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245884 q = 1) : d250902 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d250902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d250902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245885 q = 1) : d250903 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d250903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d250903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245886 q = 1) : d250904 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d250904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d250904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62782 (p : Pattern) (ha : d152855 p = 1) (hb : d245892 p = 1) : d250910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d245887 q = 1) : d250905 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d250905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62781 q ha hb
    | true =>
      simp only [d245887, d250905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d245888 q = 1) : d250906 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d250906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d250906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d245889 q = 1) : d250907 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d250907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d250907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d245890 q = 1) : d250908 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d250908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d250908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d245891 q = 1) : d250909 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d250909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d250909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d245892 q = 1) : d250910 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d250910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d250910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62783 (p : Pattern) (ha : d156617 p = 1) (hb : d247421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118715 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d247416 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156613 q = 1) (hb : d247417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d247417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156613, d247417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118633 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156614 q = 1) (hb : d247418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d247418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156614, d247418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156615 q = 1) (hb : d247419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d247419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156615, d247419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156616 q = 1) (hb : d247420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d247420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156616, d247420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156617 q = 1) (hb : d247421 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156617, d247421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156617, d247421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62784 (p : Pattern) (ha : d156624 p = 1) (hb : d247428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118709 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d118715 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d156613 q = 1) (hb : d247417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d247417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156613, d247417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118633 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156614 q = 1) (hb : d247418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d247418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156614, d247418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156615 q = 1) (hb : d247419 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d247419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156615, d247419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156616 q = 1) (hb : d247420 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d247420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156616, d247420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d118743 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d118747 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d247423 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d156620 q = 1) (hb : d247424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d247424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156620, d247424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d118640 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d156621 q = 1) (hb : d247425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d247425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d156621, d247425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156622 q = 1) (hb : d247426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d247426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156622, d247426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156623 q = 1) (hb : d247427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d247427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156623, d247427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d156624 q = 1) (hb : d247428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156624, d247428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156624, d247428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62785 (p : Pattern) (ha : d156818 p = 1) (hb : d247435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247423 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156620 q = 1) (hb : d247424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d247424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156620, d247424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118640 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156621 q = 1) (hb : d247425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d247425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156621, d247425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156622 q = 1) (hb : d247433 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d247433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156622, d247433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156623 q = 1) (hb : d247434 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d247434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156623, d247434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156818 q = 1) (hb : d247435 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156818, d247435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156818, d247435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62786 (p : Pattern) (ha : d156859 p = 1) (hb : d247463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d118672 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q ha hb
    | true =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156855 q = 1) (hb : d247459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156855, d247459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156855, d247459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d118673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156856 q = 1) (hb : d247460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156856, d247460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156856, d247460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156857 q = 1) (hb : d247461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156857, d247461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156857, d247461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156858 q = 1) (hb : d247462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156858, d247462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156858, d247462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156859 q = 1) (hb : d247463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156859, d247463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156859, d247463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62787 (p : Pattern) (ha : d158042 p = 1) (hb : d247469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118703 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156625 q = 1) (hb : d247429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156625, d247429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62783 q ha hb
    | true =>
      simp only [d156625, d247429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62784 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d118757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156626 q = 1) (hb : d247430 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156626, d247430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156626, d247430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158032 q = 1) (hb : d247431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158032, d247431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158032, d247431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158033 q = 1) (hb : d247432 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158033, d247432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158033, d247432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156819 q = 1) (hb : d247436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156819, d247436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156819, d247436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62785 q ha hb
  have h8 (q : Pattern) (ha : d158034 q = 1) (hb : d247437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158034, d247437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158034, d247437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d158035 q = 1) (hb : d247438 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158035, d247438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d158035, d247438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d158036 q = 1) (hb : d247439 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158036, d247439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158036, d247439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158037 q = 1) (hb : d247440 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158037, d247440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158037, d247440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156860 q = 1) (hb : d247464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156860, d247464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156860, d247464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62786 q ha hb
  have h13 (q : Pattern) (ha : d158038 q = 1) (hb : d247465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158038, d247465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158038, d247465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d158039 q = 1) (hb : d247466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158039, d247466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158039, d247466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d158040 q = 1) (hb : d247467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158040, d247467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d158040, d247467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d158041 q = 1) (hb : d247468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158041, d247468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158041, d247468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158042 q = 1) (hb : d247469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158042, d247469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d158042, d247469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62788 (p : Pattern) (ha : d158048 p = 1) (hb : d247475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d118688 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d158043 q = 1) (hb : d247470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158043, d247470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158043, d247470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62787 q ha hb
  have h3 (q : Pattern) (ha : d158044 q = 1) (hb : d247471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158044, d247471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158044, d247471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158045 q = 1) (hb : d247472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158045, d247472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158045, d247472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158046 q = 1) (hb : d247473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158046, d247473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158046, d247473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158047 q = 1) (hb : d247474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158047, d247474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158047, d247474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158048 q = 1) (hb : d247475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158048, d247475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158048, d247475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62789 (p : Pattern) (ha : d156735 p = 1) (hb : d247531 p = 1) : d249780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d247520 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h5 (q : Pattern) (ha : d156731 q = 1) (hb : d247521 q = 1) : d249776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d247521, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156731, d247521, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d247527 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156732 q = 1) (hb : d247528 q = 1) : d249777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d247528, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156732, d247528, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156733 q = 1) (hb : d247529 q = 1) : d249778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d247529, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156733, d247529, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156734 q = 1) (hb : d247530 q = 1) : d249779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d247530, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156734, d247530, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156735 q = 1) (hb : d247531 q = 1) : d249780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156735, d247531, d249780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156735, d247531, d249780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62790 (p : Pattern) (ha : d156742 p = 1) (hb : d247550 p = 1) : d249787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247502 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247520 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h4 (q : Pattern) (ha : d156731 q = 1) (hb : d247521 q = 1) : d249776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d247521, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156731, d247521, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d247527 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156732 q = 1) (hb : d247528 q = 1) : d249777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d247528, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156732, d247528, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156733 q = 1) (hb : d247529 q = 1) : d249778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d247529, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156733, d247529, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156734 q = 1) (hb : d247530 q = 1) : d249779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d247530, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d247530, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247536 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247540 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d247542 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d156675 q = 1) (hb : d247423 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q ha hb
    | true =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q hb ha
  have h13 (q : Pattern) (ha : d156738 q = 1) (hb : d247543 q = 1) : d249783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d247543, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156738, d247543, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247546 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156739 q = 1) (hb : d247547 q = 1) : d249784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d247547, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156739, d247547, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156740 q = 1) (hb : d247548 q = 1) : d249785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d247548, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156740, d247548, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156741 q = 1) (hb : d247549 q = 1) : d249786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d247549, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156741, d247549, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156742 q = 1) (hb : d247550 q = 1) : d249787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156742, d247550, d249787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156742, d247550, d249787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62791 (p : Pattern) (ha : d158051 p = 1) (hb : d247559 p = 1) : d250913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156675 q = 1) (hb : d247423 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q ha hb
    | true =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q hb ha
  have h3 (q : Pattern) (ha : d156738 q = 1) (hb : d247543 q = 1) : d249783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d247543, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156738, d247543, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247546 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156739 q = 1) (hb : d247547 q = 1) : d249784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d247547, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156739, d247547, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156740 q = 1) (hb : d247557 q = 1) : d249785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d247557, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156740, d247557, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156741 q = 1) (hb : d247558 q = 1) : d249786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d247558, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156741, d247558, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158051 q = 1) (hb : d247559 q = 1) : d250913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158051, d247559, d250913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158051, d247559, d250913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62792 (p : Pattern) (ha : d158061 p = 1) (hb : d247593 p = 1) : d250923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156713 q = 1) (hb : d247458 q = 1) : d249758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156713, d247458, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62498 q ha hb
    | true =>
      simp only [d156713, d247458, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q hb ha
  have h3 (q : Pattern) (ha : d158057 q = 1) (hb : d247583 q = 1) : d250919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158057, d247583, d250919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158057, d247583, d250919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247589 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158058 q = 1) (hb : d247590 q = 1) : d250920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158058, d247590, d250920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158058, d247590, d250920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158059 q = 1) (hb : d247591 q = 1) : d250921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158059, d247591, d250921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158059, d247591, d250921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158060 q = 1) (hb : d247592 q = 1) : d250922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158060, d247592, d250922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158060, d247592, d250922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158061 q = 1) (hb : d247593 q = 1) : d250923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158061, d247593, d250923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158061, d247593, d250923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62793 (p : Pattern) (ha : d158067 p = 1) (hb : d247599 p = 1) : d250929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247490 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156743 q = 1) (hb : d247551 q = 1) : d249788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156743, d247551, d249788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62789 q ha hb
    | true =>
      simp only [d156743, d247551, d249788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62790 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247553 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156744 q = 1) (hb : d247554 q = 1) : d249789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156744, d247554, d249789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156744, d247554, d249789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158049 q = 1) (hb : d247555 q = 1) : d250911 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158049, d247555, d250911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158049, d247555, d250911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158050 q = 1) (hb : d247556 q = 1) : d250912 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158050, d247556, d250912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158050, d247556, d250912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158052 q = 1) (hb : d247560 q = 1) : d250914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158052, d247560, d250914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158052, d247560, d250914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62791 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d118890 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158053 q = 1) (hb : d247561 q = 1) : d250915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158053, d247561, d250915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158053, d247561, d250915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158054 q = 1) (hb : d247562 q = 1) : d250916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158054, d247562, d250916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158054, d247562, d250916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158055 q = 1) (hb : d247563 q = 1) : d250917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158055, d247563, d250917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158055, d247563, d250917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158056 q = 1) (hb : d247564 q = 1) : d250918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158056, d247564, d250918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158056, d247564, d250918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158062 q = 1) (hb : d247594 q = 1) : d250924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158062, d247594, d250924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158062, d247594, d250924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62792 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d118930 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158063 q = 1) (hb : d247595 q = 1) : d250925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158063, d247595, d250925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158063, d247595, d250925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158064 q = 1) (hb : d247596 q = 1) : d250926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158064, d247596, d250926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158064, d247596, d250926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158065 q = 1) (hb : d247597 q = 1) : d250927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158065, d247597, d250927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158065, d247597, d250927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158066 q = 1) (hb : d247598 q = 1) : d250928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158066, d247598, d250928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158066, d247598, d250928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158067 q = 1) (hb : d247599 q = 1) : d250929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158067, d247599, d250929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158067, d247599, d250929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62794 (p : Pattern) (ha : d158073 p = 1) (hb : d247605 p = 1) : d250935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158068 q = 1) (hb : d247600 q = 1) : d250930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158068, d247600, d250930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158068, d247600, d250930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62793 q ha hb
  have h2 (q : Pattern) (ha : d158069 q = 1) (hb : d247601 q = 1) : d250931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158069, d247601, d250931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158069, d247601, d250931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158070 q = 1) (hb : d247602 q = 1) : d250932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158070, d247602, d250932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158070, d247602, d250932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158071 q = 1) (hb : d247603 q = 1) : d250933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158071, d247603, d250933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158071, d247603, d250933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158072 q = 1) (hb : d247604 q = 1) : d250934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158072, d247604, d250934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158072, d247604, d250934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158073 q = 1) (hb : d247605 q = 1) : d250935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158073, d247605, d250935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158073, d247605, d250935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62795 (p : Pattern) (ha : d247678 p = 1) (hb : d248691 p = 1) : d249914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247649 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d247667 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d247620 q = 1) (hb : d248686 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
    | true =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
  have h5 (q : Pattern) (ha : d247668 q = 1) (hb : d248687 q = 1) : d249910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247668, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d247668, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d247674 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d247675 q = 1) (hb : d248688 q = 1) : d249911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247675, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247675, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d247676 q = 1) (hb : d248689 q = 1) : d249912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247676, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d247676, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247677 q = 1) (hb : d248690 q = 1) : d249913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247677, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247677, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247678 q = 1) (hb : d248691 q = 1) : d249914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247678, d248691, d249914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247678, d248691, d249914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62796 (p : Pattern) (ha : d247697 p = 1) (hb : d248700 p = 1) : d249923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247620 q = 1) (hb : d248686 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
    | true =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
  have h4 (q : Pattern) (ha : d247668 q = 1) (hb : d248687 q = 1) : d249910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247668, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d247668, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d247674 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d247675 q = 1) (hb : d248688 q = 1) : d249911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247675, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247675, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d247676 q = 1) (hb : d248689 q = 1) : d249912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247676, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247676, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247677 q = 1) (hb : d248690 q = 1) : d249913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247677, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247677, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247683 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247687 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d247689 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d247629 q = 1) (hb : d248695 q = 1) : d249918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62545 q ha hb
    | true =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62533 q ha hb
  have h13 (q : Pattern) (ha : d247690 q = 1) (hb : d248696 q = 1) : d249919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247690, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d247690, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247693 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247694 q = 1) (hb : d248697 q = 1) : d249920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247694, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247694, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d247695 q = 1) (hb : d248698 q = 1) : d249921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247695, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d247695, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d247696 q = 1) (hb : d248699 q = 1) : d249922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247696, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d247696, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d247697 q = 1) (hb : d248700 q = 1) : d249923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247697, d248700, d249923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247697, d248700, d249923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62797 (p : Pattern) (ha : d247706 p = 1) (hb : d250752 p = 1) : d250939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247629 q = 1) (hb : d248695 q = 1) : d249918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62545 q ha hb
    | true =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62533 q ha hb
  have h3 (q : Pattern) (ha : d247690 q = 1) (hb : d248696 q = 1) : d249919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247690, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247690, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247693 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d247694 q = 1) (hb : d248697 q = 1) : d249920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247694, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247694, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247704 q = 1) (hb : d248698 q = 1) : d249921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247704, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247704, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247705 q = 1) (hb : d248699 q = 1) : d249922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247705, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247705, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247706 q = 1) (hb : d250752 q = 1) : d250939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247706, d250752, d250939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247706, d250752, d250939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62798 (p : Pattern) (ha : d247754 p = 1) (hb : d250763 p = 1) : d250949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247742 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247743 q = 1) (hb : d250758 q = 1) : d250030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247743, d250758, d250030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62574 q ha hb
    | true =>
      simp only [d247743, d250758, d250030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62538 q ha hb
  have h3 (q : Pattern) (ha : d247744 q = 1) (hb : d250759 q = 1) : d250945 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247744, d250759, d250945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247744, d250759, d250945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d247751 q = 1) (hb : d250760 q = 1) : d250946 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247751, d250760, d250946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247751, d250760, d250946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247752 q = 1) (hb : d250761 q = 1) : d250947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247752, d250761, d250947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247752, d250761, d250947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247753 q = 1) (hb : d250762 q = 1) : d250948 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247753, d250762, d250948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247753, d250762, d250948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247754 q = 1) (hb : d250763 q = 1) : d250949 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247754, d250763, d250949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247754, d250763, d250949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62799 (p : Pattern) (ha : d247760 p = 1) (hb : d250769 p = 1) : d250955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247698 q = 1) (hb : d248701 q = 1) : d249924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247698, d248701, d249924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62795 q ha hb
    | true =>
      simp only [d247698, d248701, d249924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62796 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247700 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247701 q = 1) (hb : d248702 q = 1) : d249925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247701, d248702, d249925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247701, d248702, d249925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d247702 q = 1) (hb : d250750 q = 1) : d250937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247702, d250750, d250937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247702, d250750, d250937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247703 q = 1) (hb : d250751 q = 1) : d250938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247703, d250751, d250938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247703, d250751, d250938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247707 q = 1) (hb : d250753 q = 1) : d250940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247707, d250753, d250940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d247707, d250753, d250940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62797 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119084 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d247708 q = 1) (hb : d250754 q = 1) : d250941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247708, d250754, d250941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247708, d250754, d250941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d247709 q = 1) (hb : d250755 q = 1) : d250942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247709, d250755, d250942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247709, d250755, d250942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d247710 q = 1) (hb : d250756 q = 1) : d250943 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247710, d250756, d250943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247710, d250756, d250943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d247711 q = 1) (hb : d250757 q = 1) : d250944 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247711, d250757, d250944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247711, d250757, d250944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d247755 q = 1) (hb : d250764 q = 1) : d250950 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247755, d250764, d250950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d247755, d250764, d250950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62798 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d119159 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247756 q = 1) (hb : d250765 q = 1) : d250951 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247756, d250765, d250951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247756, d250765, d250951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d247757 q = 1) (hb : d250766 q = 1) : d250952 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247757, d250766, d250952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247757, d250766, d250952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d247758 q = 1) (hb : d250767 q = 1) : d250953 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247758, d250767, d250953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d247758, d250767, d250953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d247759 q = 1) (hb : d250768 q = 1) : d250954 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247759, d250768, d250954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d247759, d250768, d250954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d247760 q = 1) (hb : d250769 q = 1) : d250955 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d247760, d250769, d250955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d247760, d250769, d250955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62800 (p : Pattern) (ha : d247766 p = 1) (hb : d250775 p = 1) : d250961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247761 q = 1) (hb : d250770 q = 1) : d250956 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d247761, d250770, d250956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247761, d250770, d250956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62799 q ha hb
  have h2 (q : Pattern) (ha : d247762 q = 1) (hb : d250771 q = 1) : d250957 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d247762, d250771, d250957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247762, d250771, d250957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247763 q = 1) (hb : d250772 q = 1) : d250958 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d247763, d250772, d250958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247763, d250772, d250958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247764 q = 1) (hb : d250773 q = 1) : d250959 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d247764, d250773, d250959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247764, d250773, d250959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247765 q = 1) (hb : d250774 q = 1) : d250960 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d247765, d250774, d250960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247765, d250774, d250960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247766 q = 1) (hb : d250775 q = 1) : d250961 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d247766, d250775, d250961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247766, d250775, d250961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62801 (p : Pattern) (ha : d247880 p = 1) (hb : d248903 p = 1) : d250081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d247861 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d247808 q = 1) (hb : d248898 q = 1) : d250076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
    | true =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
  have h5 (q : Pattern) (ha : d247862 q = 1) (hb : d248899 q = 1) : d250077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247862, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d247862, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d247876 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d247877 q = 1) (hb : d248900 q = 1) : d250078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247877, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247877, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d247878 q = 1) (hb : d248901 q = 1) : d250079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247878, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d247878, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247879 q = 1) (hb : d248902 q = 1) : d250080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247879, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247879, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247880 q = 1) (hb : d248903 q = 1) : d250081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247880, d248903, d250081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247880, d248903, d250081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62802 (p : Pattern) (ha : d247901 p = 1) (hb : d248913 p = 1) : d250091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247861 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247808 q = 1) (hb : d248898 q = 1) : d250076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
    | true =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
  have h4 (q : Pattern) (ha : d247862 q = 1) (hb : d248899 q = 1) : d250077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247862, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d247862, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d247876 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d247877 q = 1) (hb : d248900 q = 1) : d250078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247877, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247877, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d247878 q = 1) (hb : d248901 q = 1) : d250079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247878, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247878, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247879 q = 1) (hb : d248902 q = 1) : d250080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247879, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247879, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247886 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247891 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d247893 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d247818 q = 1) (hb : d248908 q = 1) : d250086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62592 q ha hb
    | true =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62593 q ha hb
  have h13 (q : Pattern) (ha : d247894 q = 1) (hb : d248909 q = 1) : d250087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247894, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d247894, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247897 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247898 q = 1) (hb : d248910 q = 1) : d250088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247898, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247898, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d247899 q = 1) (hb : d248911 q = 1) : d250089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247899, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d247899, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d247900 q = 1) (hb : d248912 q = 1) : d250090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247900, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d247900, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d247901 q = 1) (hb : d248913 q = 1) : d250091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247901, d248913, d250091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247901, d248913, d250091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62803 (p : Pattern) (ha : d247921 p = 1) (hb : d250780 p = 1) : d250966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247818 q = 1) (hb : d248908 q = 1) : d250086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62592 q ha hb
    | true =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62593 q ha hb
  have h3 (q : Pattern) (ha : d247894 q = 1) (hb : d248909 q = 1) : d250087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247894, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247894, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247897 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d247898 q = 1) (hb : d248910 q = 1) : d250088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247898, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247898, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247919 q = 1) (hb : d248911 q = 1) : d250089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247919, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247919, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247920 q = 1) (hb : d248912 q = 1) : d250090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247920, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247920, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247921 q = 1) (hb : d250780 q = 1) : d250966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247921, d250780, d250966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247921, d250780, d250966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62804 (p : Pattern) (ha : d248005 p = 1) (hb : d250791 p = 1) : d250977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247986 q = 1) (hb : d250786 q = 1) : d250972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247986, d250786, d250972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62628 q ha hb
    | true =>
      simp only [d247986, d250786, d250972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62632 q ha hb
  have h3 (q : Pattern) (ha : d247987 q = 1) (hb : d250787 q = 1) : d250973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247987, d250787, d250973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247987, d250787, d250973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248002 q = 1) (hb : d250788 q = 1) : d250974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248002, d250788, d250974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248002, d250788, d250974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248003 q = 1) (hb : d250789 q = 1) : d250975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248003, d250789, d250975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248003, d250789, d250975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248004 q = 1) (hb : d250790 q = 1) : d250976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248004, d250790, d250976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248004, d250790, d250976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248005 q = 1) (hb : d250791 q = 1) : d250977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248005, d250791, d250977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248005, d250791, d250977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62805 (p : Pattern) (ha : d248018 p = 1) (hb : d250797 p = 1) : d250983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247826 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247902 q = 1) (hb : d248914 q = 1) : d250092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247902, d248914, d250092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62801 q ha hb
    | true =>
      simp only [d247902, d248914, d250092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62802 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247915 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247916 q = 1) (hb : d248915 q = 1) : d250093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247916, d248915, d250093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247916, d248915, d250093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d247917 q = 1) (hb : d250778 q = 1) : d250964 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247917, d250778, d250964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247917, d250778, d250964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247918 q = 1) (hb : d250779 q = 1) : d250965 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247918, d250779, d250965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247918, d250779, d250965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247922 q = 1) (hb : d250781 q = 1) : d250967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247922, d250781, d250967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d247922, d250781, d250967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62803 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d247924 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d247925 q = 1) (hb : d250782 q = 1) : d250968 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247925, d250782, d250968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247925, d250782, d250968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d247926 q = 1) (hb : d250783 q = 1) : d250969 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247926, d250783, d250969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247926, d250783, d250969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d247927 q = 1) (hb : d250784 q = 1) : d250970 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247927, d250784, d250970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247927, d250784, d250970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d247928 q = 1) (hb : d250785 q = 1) : d250971 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247928, d250785, d250971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247928, d250785, d250971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248006 q = 1) (hb : d250792 q = 1) : d250978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248006, d250792, d250978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248006, d250792, d250978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62804 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248013 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248014 q = 1) (hb : d250793 q = 1) : d250979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248014, d250793, d250979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248014, d250793, d250979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d248015 q = 1) (hb : d250794 q = 1) : d250980 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248015, d250794, d250980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248015, d250794, d250980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d248016 q = 1) (hb : d250795 q = 1) : d250981 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248016, d250795, d250981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248016, d250795, d250981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d248017 q = 1) (hb : d250796 q = 1) : d250982 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248017, d250796, d250982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248017, d250796, d250982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d248018 q = 1) (hb : d250797 q = 1) : d250983 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248018, d250797, d250983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d248018, d250797, d250983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62806 (p : Pattern) (ha : d248024 p = 1) (hb : d250803 p = 1) : d250989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248019 q = 1) (hb : d250798 q = 1) : d250984 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248019, d250798, d250984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248019, d250798, d250984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62805 q ha hb
  have h2 (q : Pattern) (ha : d248020 q = 1) (hb : d250799 q = 1) : d250985 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248020, d250799, d250985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248020, d250799, d250985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248021 q = 1) (hb : d250800 q = 1) : d250986 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248021, d250800, d250986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248021, d250800, d250986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248022 q = 1) (hb : d250801 q = 1) : d250987 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248022, d250801, d250987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248022, d250801, d250987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248023 q = 1) (hb : d250802 q = 1) : d250988 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248023, d250802, d250988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248023, d250802, d250988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248024 q = 1) (hb : d250803 q = 1) : d250989 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248024, d250803, d250989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248024, d250803, d250989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62807 (p : Pattern) (ha : d248139 p = 1) (hb : d249179 p = 1) : d250303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d248120 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d248067 q = 1) (hb : d249174 q = 1) : d250298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
    | true =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
  have h5 (q : Pattern) (ha : d248121 q = 1) (hb : d249175 q = 1) : d250299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248121, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d248121, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d248135 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248136 q = 1) (hb : d249176 q = 1) : d250300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248136, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248136, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d248137 q = 1) (hb : d249177 q = 1) : d250301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248137, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d248137, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248138 q = 1) (hb : d249178 q = 1) : d250302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248138, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248138, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248139 q = 1) (hb : d249179 q = 1) : d250303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248139, d249179, d250303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248139, d249179, d250303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62808 (p : Pattern) (ha : d248160 p = 1) (hb : d249189 p = 1) : d250313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d248093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248120 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248067 q = 1) (hb : d249174 q = 1) : d250298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
    | true =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
  have h4 (q : Pattern) (ha : d248121 q = 1) (hb : d249175 q = 1) : d250299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248121, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d248121, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d248135 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d248136 q = 1) (hb : d249176 q = 1) : d250300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248136, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248136, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d248137 q = 1) (hb : d249177 q = 1) : d250301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248137, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248137, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248138 q = 1) (hb : d249178 q = 1) : d250302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248138, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248138, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248145 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d248150 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d248152 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d248077 q = 1) (hb : d249184 q = 1) : d250308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62649 q ha hb
    | true =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62650 q ha hb
  have h13 (q : Pattern) (ha : d248153 q = 1) (hb : d249185 q = 1) : d250309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248153, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d248153, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248156 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248157 q = 1) (hb : d249186 q = 1) : d250310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248157, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248157, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d248158 q = 1) (hb : d249187 q = 1) : d250311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248158, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d248158, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248159 q = 1) (hb : d249188 q = 1) : d250312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248159, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d248159, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248160 q = 1) (hb : d249189 q = 1) : d250313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248160, d249189, d250313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248160, d249189, d250313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62809 (p : Pattern) (ha : d248180 p = 1) (hb : d250809 p = 1) : d250995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248152 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d248077 q = 1) (hb : d249184 q = 1) : d250308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62649 q ha hb
    | true =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62650 q ha hb
  have h3 (q : Pattern) (ha : d248153 q = 1) (hb : d249185 q = 1) : d250309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248153, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248153, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248156 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248157 q = 1) (hb : d249186 q = 1) : d250310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248157, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248157, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248178 q = 1) (hb : d249187 q = 1) : d250311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248178, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248178, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248179 q = 1) (hb : d249188 q = 1) : d250312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248179, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248179, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248180 q = 1) (hb : d250809 q = 1) : d250995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248180, d250809, d250995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248180, d250809, d250995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62810 (p : Pattern) (ha : d248264 p = 1) (hb : d250820 p = 1) : d251006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d248245 q = 1) (hb : d250815 q = 1) : d251001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248245, d250815, d251001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62684 q ha hb
    | true =>
      simp only [d248245, d250815, d251001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62688 q ha hb
  have h3 (q : Pattern) (ha : d248246 q = 1) (hb : d250816 q = 1) : d251002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248246, d250816, d251002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248246, d250816, d251002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248260 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248261 q = 1) (hb : d250817 q = 1) : d251003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248261, d250817, d251003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248261, d250817, d251003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248262 q = 1) (hb : d250818 q = 1) : d251004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248262, d250818, d251004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248262, d250818, d251004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248263 q = 1) (hb : d250819 q = 1) : d251005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248263, d250819, d251005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248263, d250819, d251005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248264 q = 1) (hb : d250820 q = 1) : d251006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248264, d250820, d251006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248264, d250820, d251006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62811 (p : Pattern) (ha : d248277 p = 1) (hb : d250826 p = 1) : d251012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d248085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248161 q = 1) (hb : d249190 q = 1) : d250314 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248161, d249190, d250314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62807 q ha hb
    | true =>
      simp only [d248161, d249190, d250314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62808 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248174 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248175 q = 1) (hb : d249191 q = 1) : d250315 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248175, d249191, d250315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248175, d249191, d250315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248176 q = 1) (hb : d250807 q = 1) : d250993 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248176, d250807, d250993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248176, d250807, d250993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248177 q = 1) (hb : d250808 q = 1) : d250994 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248177, d250808, d250994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248177, d250808, d250994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248181 q = 1) (hb : d250810 q = 1) : d250996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248181, d250810, d250996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248181, d250810, d250996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62809 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d248183 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d248184 q = 1) (hb : d250811 q = 1) : d250997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248184, d250811, d250997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248184, d250811, d250997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d248185 q = 1) (hb : d250812 q = 1) : d250998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248185, d250812, d250998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248185, d250812, d250998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d248186 q = 1) (hb : d250813 q = 1) : d250999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248186, d250813, d250999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248186, d250813, d250999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d248187 q = 1) (hb : d250814 q = 1) : d251000 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248187, d250814, d251000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248187, d250814, d251000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248265 q = 1) (hb : d250821 q = 1) : d251007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248265, d250821, d251007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248265, d250821, d251007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62810 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248272 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248273 q = 1) (hb : d250822 q = 1) : d251008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248273, d250822, d251008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248273, d250822, d251008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d248274 q = 1) (hb : d250823 q = 1) : d251009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248274, d250823, d251009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248274, d250823, d251009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d248275 q = 1) (hb : d250824 q = 1) : d251010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248275, d250824, d251010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248275, d250824, d251010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d248276 q = 1) (hb : d250825 q = 1) : d251011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248276, d250825, d251011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248276, d250825, d251011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d248277 q = 1) (hb : d250826 q = 1) : d251012 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248277, d250826, d251012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d248277, d250826, d251012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62812 (p : Pattern) (ha : d248283 p = 1) (hb : d250832 p = 1) : d251018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248278 q = 1) (hb : d250827 q = 1) : d251013 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248278, d250827, d251013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248278, d250827, d251013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62811 q ha hb
  have h2 (q : Pattern) (ha : d248279 q = 1) (hb : d250828 q = 1) : d251014 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248279, d250828, d251014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248279, d250828, d251014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248280 q = 1) (hb : d250829 q = 1) : d251015 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248280, d250829, d251015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248280, d250829, d251015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248281 q = 1) (hb : d250830 q = 1) : d251016 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248281, d250830, d251016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248281, d250830, d251016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248282 q = 1) (hb : d250831 q = 1) : d251017 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248282, d250831, d251017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248282, d250831, d251017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248283 q = 1) (hb : d250832 q = 1) : d251018 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248283, d250832, d251018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248283, d250832, d251018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62813 (p : Pattern) (ha : d248395 p = 1) (hb : d249450 p = 1) : d250520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d248376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d248327 q = 1) (hb : d249445 q = 1) : d250515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
    | true =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
  have h5 (q : Pattern) (ha : d248377 q = 1) (hb : d249446 q = 1) : d250516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248377, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d248377, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d248391 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248392 q = 1) (hb : d249447 q = 1) : d250517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248392, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248392, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d248393 q = 1) (hb : d249448 q = 1) : d250518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248393, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d248393, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248394 q = 1) (hb : d249449 q = 1) : d250519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248394, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248394, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248395 q = 1) (hb : d249450 q = 1) : d250520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248395, d249450, d250520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248395, d249450, d250520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62814 (p : Pattern) (ha : d248416 p = 1) (hb : d249460 p = 1) : d250530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d248353 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248362 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248327 q = 1) (hb : d249445 q = 1) : d250515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
    | true =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
  have h4 (q : Pattern) (ha : d248377 q = 1) (hb : d249446 q = 1) : d250516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248377, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d248377, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d248391 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d248392 q = 1) (hb : d249447 q = 1) : d250517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248392, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248392, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d248393 q = 1) (hb : d249448 q = 1) : d250518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248393, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248393, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248394 q = 1) (hb : d249449 q = 1) : d250519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248394, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248394, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d248406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d248408 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d248337 q = 1) (hb : d249455 q = 1) : d250525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62703 q ha hb
    | true =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62704 q ha hb
  have h13 (q : Pattern) (ha : d248409 q = 1) (hb : d249456 q = 1) : d250526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248409, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d248409, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248412 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248413 q = 1) (hb : d249457 q = 1) : d250527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248413, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248413, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d248414 q = 1) (hb : d249458 q = 1) : d250528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248414, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d248414, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248415 q = 1) (hb : d249459 q = 1) : d250529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248415, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d248415, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248416 q = 1) (hb : d249460 q = 1) : d250530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248416, d249460, d250530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248416, d249460, d250530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62815 (p : Pattern) (ha : d248436 p = 1) (hb : d250839 p = 1) : d251025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d248337 q = 1) (hb : d249455 q = 1) : d250525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62703 q ha hb
    | true =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62704 q ha hb
  have h3 (q : Pattern) (ha : d248409 q = 1) (hb : d249456 q = 1) : d250526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248409, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248409, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248412 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248413 q = 1) (hb : d249457 q = 1) : d250527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248413, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248413, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248434 q = 1) (hb : d249458 q = 1) : d250528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248434, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248434, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248435 q = 1) (hb : d249459 q = 1) : d250529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248435, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248435, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248436 q = 1) (hb : d250839 q = 1) : d251025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248436, d250839, d251025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248436, d250839, d251025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62816 (p : Pattern) (ha : d248516 p = 1) (hb : d250850 p = 1) : d251036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d248492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d248497 q = 1) (hb : d250845 q = 1) : d251031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248497, d250845, d251031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62735 q ha hb
    | true =>
      simp only [d248497, d250845, d251031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62739 q ha hb
  have h3 (q : Pattern) (ha : d248498 q = 1) (hb : d250846 q = 1) : d251032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248498, d250846, d251032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248498, d250846, d251032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248513 q = 1) (hb : d250847 q = 1) : d251033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248513, d250847, d251033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248513, d250847, d251033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248514 q = 1) (hb : d250848 q = 1) : d251034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248514, d250848, d251034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248514, d250848, d251034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248515 q = 1) (hb : d250849 q = 1) : d251035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248515, d250849, d251035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248515, d250849, d251035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248516 q = 1) (hb : d250850 q = 1) : d251036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248516, d250850, d251036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248516, d250850, d251036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62817 (p : Pattern) (ha : d248529 p = 1) (hb : d250856 p = 1) : d251042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d248345 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248417 q = 1) (hb : d249461 q = 1) : d250531 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248417, d249461, d250531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62813 q ha hb
    | true =>
      simp only [d248417, d249461, d250531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62814 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248430 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248431 q = 1) (hb : d249462 q = 1) : d250532 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248431, d249462, d250532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248431, d249462, d250532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248432 q = 1) (hb : d250837 q = 1) : d251023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248432, d250837, d251023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248432, d250837, d251023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d248433 q = 1) (hb : d250838 q = 1) : d251024 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248433, d250838, d251024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248433, d250838, d251024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248437 q = 1) (hb : d250840 q = 1) : d251026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248437, d250840, d251026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248437, d250840, d251026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62815 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d248439 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d248440 q = 1) (hb : d250841 q = 1) : d251027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248440, d250841, d251027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248440, d250841, d251027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d248441 q = 1) (hb : d250842 q = 1) : d251028 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248441, d250842, d251028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248441, d250842, d251028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d248442 q = 1) (hb : d250843 q = 1) : d251029 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248442, d250843, d251029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248442, d250843, d251029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d248443 q = 1) (hb : d250844 q = 1) : d251030 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248443, d250844, d251030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248443, d250844, d251030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248517 q = 1) (hb : d250851 q = 1) : d251037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248517, d250851, d251037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248517, d250851, d251037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62816 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248524 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248525 q = 1) (hb : d250852 q = 1) : d251038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248525, d250852, d251038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248525, d250852, d251038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d248526 q = 1) (hb : d250853 q = 1) : d251039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248526, d250853, d251039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248526, d250853, d251039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d248527 q = 1) (hb : d250854 q = 1) : d251040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248527, d250854, d251040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248527, d250854, d251040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d248528 q = 1) (hb : d250855 q = 1) : d251041 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248528, d250855, d251041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248528, d250855, d251041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d248529 q = 1) (hb : d250856 q = 1) : d251042 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248529, d250856, d251042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d248529, d250856, d251042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62818 (p : Pattern) (ha : d248535 p = 1) (hb : d250862 p = 1) : d251048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248530 q = 1) (hb : d250857 q = 1) : d251043 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248530, d250857, d251043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248530, d250857, d251043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62817 q ha hb
  have h2 (q : Pattern) (ha : d248531 q = 1) (hb : d250858 q = 1) : d251044 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248531, d250858, d251044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248531, d250858, d251044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248532 q = 1) (hb : d250859 q = 1) : d251045 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248532, d250859, d251045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248532, d250859, d251045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248533 q = 1) (hb : d250860 q = 1) : d251046 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248533, d250860, d251046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248533, d250860, d251046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248534 q = 1) (hb : d250861 q = 1) : d251047 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248534, d250861, d251047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248534, d250861, d251047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248535 q = 1) (hb : d250862 q = 1) : d251048 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248535, d250862, d251048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248535, d250862, d251048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62819 (p : Pattern) (ha : d248541 p = 1) (hb : d250868 p = 1) : d251054 p = 1 := by
  have h0 (q : Pattern) (ha : d158074 q = 1) (hb : d247606 q = 1) : d250936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158074, d247606, d250936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62788 q ha hb
    | true =>
      simp only [d158074, d247606, d250936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62794 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247767 q = 1) (hb : d250776 q = 1) : d250962 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d247767, d250776, d250962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247767, d250776, d250962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62800 q ha hb
  have h3 (q : Pattern) (ha : d247768 q = 1) (hb : d250777 q = 1) : d250963 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d247768, d250777, d250963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247768, d250777, d250963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248025 q = 1) (hb : d250804 q = 1) : d250990 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248025, d250804, d250990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248025, d250804, d250990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62806 q ha hb
  have h5 (q : Pattern) (ha : d248026 q = 1) (hb : d250805 q = 1) : d250991 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248026, d250805, d250991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248026, d250805, d250991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248027 q = 1) (hb : d250806 q = 1) : d250992 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248027, d250806, d250992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248027, d250806, d250992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248284 q = 1) (hb : d250833 q = 1) : d251019 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248284, d250833, d251019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248284, d250833, d251019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62812 q ha hb
  have h8 (q : Pattern) (ha : d248285 q = 1) (hb : d250834 q = 1) : d251020 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248285, d250834, d251020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248285, d250834, d251020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248286 q = 1) (hb : d250835 q = 1) : d251021 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248286, d250835, d251021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248286, d250835, d251021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248287 q = 1) (hb : d250836 q = 1) : d251022 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d248287, d250836, d251022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248287, d250836, d251022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248536 q = 1) (hb : d250863 q = 1) : d251049 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248536, d250863, d251049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248536, d250863, d251049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62818 q ha hb
  have h12 (q : Pattern) (ha : d248537 q = 1) (hb : d250864 q = 1) : d251050 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248537, d250864, d251050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248537, d250864, d251050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248538 q = 1) (hb : d250865 q = 1) : d251051 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248538, d250865, d251051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248538, d250865, d251051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248539 q = 1) (hb : d250866 q = 1) : d251052 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d248539, d250866, d251052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248539, d250866, d251052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248540 q = 1) (hb : d250867 q = 1) : d251053 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d248540, d250867, d251053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248540, d250867, d251053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248541 q = 1) (hb : d250868 q = 1) : d251054 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d248541, d250868, d251054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248541, d250868, d251054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62820 (p : Pattern) (ha : d248547 p = 1) (hb : d250874 p = 1) : d251060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248542 q = 1) (hb : d250869 q = 1) : d251055 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d248542, d250869, d251055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62819 q ha hb
    | true =>
      simp only [d248542, d250869, d251055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248543 q = 1) (hb : d250870 q = 1) : d251056 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d248543, d250870, d251056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248543, d250870, d251056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248544 q = 1) (hb : d250871 q = 1) : d251057 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d248544, d250871, d251057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248544, d250871, d251057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248545 q = 1) (hb : d250872 q = 1) : d251058 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d248545, d250872, d251058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248545, d250872, d251058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248546 q = 1) (hb : d250873 q = 1) : d251059 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d248546, d250873, d251059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248546, d250873, d251059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248547 q = 1) (hb : d250874 q = 1) : d251060 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d248547, d250874, d251060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248547, d250874, d251060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62821 (p : Pattern) (ha : d248553 p = 1) (hb : d250880 p = 1) : d251066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248548 q = 1) (hb : d250875 q = 1) : d251061 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d248548, d250875, d251061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62820 q ha hb
    | true =>
      simp only [d248548, d250875, d251061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248549 q = 1) (hb : d250876 q = 1) : d251062 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d248549, d250876, d251062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248549, d250876, d251062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248550 q = 1) (hb : d250877 q = 1) : d251063 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d248550, d250877, d251063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248550, d250877, d251063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248551 q = 1) (hb : d250878 q = 1) : d251064 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d248551, d250878, d251064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248551, d250878, d251064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248552 q = 1) (hb : d250879 q = 1) : d251065 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d248552, d250879, d251065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248552, d250879, d251065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248553 q = 1) (hb : d250880 q = 1) : d251066 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d248553, d250880, d251066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248553, d250880, d251066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62822 (p : Pattern) (ha : d248559 p = 1) (hb : d250886 p = 1) : d251072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248554 q = 1) (hb : d250881 q = 1) : d251067 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d248554, d250881, d251067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62821 q ha hb
    | true =>
      simp only [d248554, d250881, d251067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248555 q = 1) (hb : d250882 q = 1) : d251068 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d248555, d250882, d251068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248555, d250882, d251068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248556 q = 1) (hb : d250883 q = 1) : d251069 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d248556, d250883, d251069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248556, d250883, d251069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248557 q = 1) (hb : d250884 q = 1) : d251070 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d248557, d250884, d251070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248557, d250884, d251070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248558 q = 1) (hb : d250885 q = 1) : d251071 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d248558, d250885, d251071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248558, d250885, d251071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248559 q = 1) (hb : d250886 q = 1) : d251072 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d248559, d250886, d251072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248559, d250886, d251072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62823 (p : Pattern) (ha : d248565 p = 1) (hb : d250892 p = 1) : d251078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248560 q = 1) (hb : d250887 q = 1) : d251073 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d248560, d250887, d251073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62822 q ha hb
    | true =>
      simp only [d248560, d250887, d251073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248561 q = 1) (hb : d250888 q = 1) : d251074 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d248561, d250888, d251074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248561, d250888, d251074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248562 q = 1) (hb : d250889 q = 1) : d251075 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d248562, d250889, d251075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248562, d250889, d251075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248563 q = 1) (hb : d250890 q = 1) : d251076 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d248563, d250890, d251076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248563, d250890, d251076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248564 q = 1) (hb : d250891 q = 1) : d251077 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d248564, d250891, d251077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248564, d250891, d251077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248565 q = 1) (hb : d250892 q = 1) : d251078 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d248565, d250892, d251078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248565, d250892, d251078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62824 (p : Pattern) (ha : d248571 p = 1) (hb : d250898 p = 1) : d251084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248566 q = 1) (hb : d250893 q = 1) : d251079 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d248566, d250893, d251079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62823 q ha hb
    | true =>
      simp only [d248566, d250893, d251079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248567 q = 1) (hb : d250894 q = 1) : d251080 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d248567, d250894, d251080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248567, d250894, d251080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248568 q = 1) (hb : d250895 q = 1) : d251081 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d248568, d250895, d251081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248568, d250895, d251081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248569 q = 1) (hb : d250896 q = 1) : d251082 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d248569, d250896, d251082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248569, d250896, d251082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248570 q = 1) (hb : d250897 q = 1) : d251083 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d248570, d250897, d251083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248570, d250897, d251083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248571 q = 1) (hb : d250898 q = 1) : d251084 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d248571, d250898, d251084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248571, d250898, d251084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62825 (p : Pattern) (ha : d248577 p = 1) (hb : d250904 p = 1) : d251090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248572 q = 1) (hb : d250899 q = 1) : d251085 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d248572, d250899, d251085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62824 q ha hb
    | true =>
      simp only [d248572, d250899, d251085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248573 q = 1) (hb : d250900 q = 1) : d251086 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d248573, d250900, d251086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248573, d250900, d251086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248574 q = 1) (hb : d250901 q = 1) : d251087 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d248574, d250901, d251087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248574, d250901, d251087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248575 q = 1) (hb : d250902 q = 1) : d251088 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d248575, d250902, d251088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248575, d250902, d251088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248576 q = 1) (hb : d250903 q = 1) : d251089 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d248576, d250903, d251089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248576, d250903, d251089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248577 q = 1) (hb : d250904 q = 1) : d251090 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d248577, d250904, d251090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248577, d250904, d251090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62826 (p : Pattern) (ha : d248583 p = 1) (hb : d250910 p = 1) : d251096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248578 q = 1) (hb : d250905 q = 1) : d251091 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d248578, d250905, d251091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62825 q ha hb
    | true =>
      simp only [d248578, d250905, d251091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248579 q = 1) (hb : d250906 q = 1) : d251092 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d248579, d250906, d251092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248579, d250906, d251092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248580 q = 1) (hb : d250907 q = 1) : d251093 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d248580, d250907, d251093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248580, d250907, d251093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248581 q = 1) (hb : d250908 q = 1) : d251094 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d248581, d250908, d251094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248581, d250908, d251094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248582 q = 1) (hb : d250909 q = 1) : d251095 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d248582, d250909, d251095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248582, d250909, d251095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248583 q = 1) (hb : d250910 q = 1) : d251096 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d248583, d250910, d251096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248583, d250910, d251096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62827 (p : Pattern) (ha : d156617 p = 1) (hb : d251101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116848 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116854 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d245910 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156613 q = 1) (hb : d251097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d251097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156613, d251097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116772 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156614 q = 1) (hb : d251098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d251098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156614, d251098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156615 q = 1) (hb : d251099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d251099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156615, d251099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156616 q = 1) (hb : d251100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d251100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156616, d251100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156617 q = 1) (hb : d251101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156617, d251101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156617, d251101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62828 (p : Pattern) (ha : d156624 p = 1) (hb : d251106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116848 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245910 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156613 q = 1) (hb : d251097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d251097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156613, d251097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d116772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156614 q = 1) (hb : d251098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d251098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156614, d251098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156615 q = 1) (hb : d251099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d251099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156615, d251099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156616 q = 1) (hb : d251100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d251100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156616, d251100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d116900 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d116904 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d245917 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d156620 q = 1) (hb : d251102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d251102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156620, d251102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d116779 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156621 q = 1) (hb : d251103 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d251103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156621, d251103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156622 q = 1) (hb : d251104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d251104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156622, d251104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156623 q = 1) (hb : d251105 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d251105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156623, d251105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156624 q = 1) (hb : d251106 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156624, d251106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156624, d251106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62829 (p : Pattern) (ha : d156818 p = 1) (hb : d251113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d245917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156620 q = 1) (hb : d251102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d251102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156620, d251102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116779 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156621 q = 1) (hb : d251103 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d251103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156621, d251103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156622 q = 1) (hb : d251111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d251111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156622, d251111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156623 q = 1) (hb : d251112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d251112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156623, d251112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156818 q = 1) (hb : d251113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156818, d251113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156818, d251113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62830 (p : Pattern) (ha : d156859 p = 1) (hb : d251123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d245952 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156855 q = 1) (hb : d251119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156855, d251119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156855, d251119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d116812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156856 q = 1) (hb : d251120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156856, d251120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156856, d251120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156857 q = 1) (hb : d251121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156857, d251121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156857, d251121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156858 q = 1) (hb : d251122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156858, d251122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156858, d251122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156859 q = 1) (hb : d251123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156859, d251123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156859, d251123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62831 (p : Pattern) (ha : d158042 p = 1) (hb : d251129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156625 q = 1) (hb : d251107 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156625, d251107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62827 q ha hb
    | true =>
      simp only [d156625, d251107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62828 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156626 q = 1) (hb : d251108 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156626, d251108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156626, d251108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158032 q = 1) (hb : d251109 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158032, d251109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158032, d251109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158033 q = 1) (hb : d251110 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158033, d251110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158033, d251110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156819 q = 1) (hb : d251114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156819, d251114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156819, d251114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62829 q ha hb
  have h8 (q : Pattern) (ha : d158034 q = 1) (hb : d251115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158034, d251115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158034, d251115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d158035 q = 1) (hb : d251116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158035, d251116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d158035, d251116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d158036 q = 1) (hb : d251117 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158036, d251117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158036, d251117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158037 q = 1) (hb : d251118 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158037, d251118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158037, d251118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156860 q = 1) (hb : d251124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156860, d251124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156860, d251124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62830 q ha hb
  have h13 (q : Pattern) (ha : d158038 q = 1) (hb : d251125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158038, d251125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158038, d251125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d158039 q = 1) (hb : d251126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158039, d251126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158039, d251126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d158040 q = 1) (hb : d251127 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158040, d251127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d158040, d251127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d158041 q = 1) (hb : d251128 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158041, d251128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158041, d251128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158042 q = 1) (hb : d251129 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158042, d251129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d158042, d251129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62832 (p : Pattern) (ha : d158048 p = 1) (hb : d251135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116827 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d158043 q = 1) (hb : d251130 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158043, d251130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158043, d251130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62831 q ha hb
  have h3 (q : Pattern) (ha : d158044 q = 1) (hb : d251131 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158044, d251131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158044, d251131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158045 q = 1) (hb : d251132 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158045, d251132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158045, d251132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158046 q = 1) (hb : d251133 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158046, d251133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158046, d251133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158047 q = 1) (hb : d251134 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158047, d251134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158047, d251134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158048 q = 1) (hb : d251135 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158048, d251135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158048, d251135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62833 (p : Pattern) (ha : d156735 p = 1) (hb : d251140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d245990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d245996 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d246014 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156731 q = 1) (hb : d251136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d251136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156731, d251136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d246039 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156732 q = 1) (hb : d251137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d251137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156732, d251137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156733 q = 1) (hb : d251138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d251138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156733, d251138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156734 q = 1) (hb : d251139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d251139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156734, d251139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156735 q = 1) (hb : d251140 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156735, d251140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156735, d251140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62834 (p : Pattern) (ha : d156742 p = 1) (hb : d251145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d245990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d245996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156731 q = 1) (hb : d251136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d251136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156731, d251136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d246039 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156732 q = 1) (hb : d251137 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d251137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156732, d251137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156733 q = 1) (hb : d251138 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d251138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156733, d251138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156734 q = 1) (hb : d251139 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d251139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d251139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d246048 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d246052 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d246054 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d156738 q = 1) (hb : d251141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d251141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156738, d251141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d246060 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156739 q = 1) (hb : d251142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d251142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156739, d251142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156740 q = 1) (hb : d251143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d251143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156740, d251143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156741 q = 1) (hb : d251144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d251144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156741, d251144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156742 q = 1) (hb : d251145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156742, d251145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156742, d251145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62835 (p : Pattern) (ha : d158051 p = 1) (hb : d251152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246054 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156738 q = 1) (hb : d251141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d251141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156738, d251141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246060 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156739 q = 1) (hb : d251142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d251142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156739, d251142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156740 q = 1) (hb : d251150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d251150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156740, d251150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156741 q = 1) (hb : d251151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d251151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156741, d251151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158051 q = 1) (hb : d251152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158051, d251152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158051, d251152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62836 (p : Pattern) (ha : d158061 p = 1) (hb : d251162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246096 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158057 q = 1) (hb : d251158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158057, d251158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158057, d251158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246121 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158058 q = 1) (hb : d251159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158058, d251159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158058, d251159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158059 q = 1) (hb : d251160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158059, d251160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158059, d251160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158060 q = 1) (hb : d251161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158060, d251161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158060, d251161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158061 q = 1) (hb : d251162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158061, d251162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158061, d251162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62837 (p : Pattern) (ha : d158067 p = 1) (hb : d251168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d245984 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156743 q = 1) (hb : d251146 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156743, d251146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62833 q ha hb
    | true =>
      simp only [d156743, d251146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62834 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246067 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156744 q = 1) (hb : d251147 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156744, d251147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156744, d251147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158049 q = 1) (hb : d251148 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158049, d251148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158049, d251148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158050 q = 1) (hb : d251149 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158050, d251149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158050, d251149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158052 q = 1) (hb : d251153 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158052, d251153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158052, d251153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62835 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d117087 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158053 q = 1) (hb : d251154 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158053, d251154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158053, d251154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158054 q = 1) (hb : d251155 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158054, d251155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158054, d251155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158055 q = 1) (hb : d251156 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158055, d251156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158055, d251156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158056 q = 1) (hb : d251157 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158056, d251157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158056, d251157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158062 q = 1) (hb : d251163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158062, d251163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158062, d251163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62836 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117145 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158063 q = 1) (hb : d251164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158063, d251164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158063, d251164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158064 q = 1) (hb : d251165 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158064, d251165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158064, d251165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158065 q = 1) (hb : d251166 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158065, d251166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158065, d251166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158066 q = 1) (hb : d251167 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158066, d251167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158066, d251167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158067 q = 1) (hb : d251168 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158067, d251168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158067, d251168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62838 (p : Pattern) (ha : d158073 p = 1) (hb : d251174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158068 q = 1) (hb : d251169 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158068, d251169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158068, d251169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62837 q ha hb
  have h2 (q : Pattern) (ha : d158069 q = 1) (hb : d251170 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158069, d251170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158069, d251170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158070 q = 1) (hb : d251171 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158070, d251171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158070, d251171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158071 q = 1) (hb : d251172 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158071, d251172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158071, d251172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158072 q = 1) (hb : d251173 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158072, d251173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158072, d251173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158073 q = 1) (hb : d251174 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158073, d251174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158073, d251174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62839 (p : Pattern) (ha : d248691 p = 1) (hb : d251180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d246199 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248687 q = 1) (hb : d251176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248687, d251176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248687, d251176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d246224 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248688 q = 1) (hb : d251177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248688, d251177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248688, d251177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248689 q = 1) (hb : d251178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248689, d251178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248689, d251178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248690 q = 1) (hb : d251179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248690, d251179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248690, d251179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248691 q = 1) (hb : d251180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248691, d251180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248691, d251180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62840 (p : Pattern) (ha : d248700 p = 1) (hb : d251185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246199 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d248686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d248687 q = 1) (hb : d251176 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248687, d251176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248687, d251176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d246224 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d248688 q = 1) (hb : d251177 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248688, d251177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248688, d251177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248689 q = 1) (hb : d251178 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248689, d251178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248689, d251178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248690 q = 1) (hb : d251179 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248690, d251179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248690, d251179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d246233 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d246237 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d246239 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d248695 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d248696 q = 1) (hb : d251181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248696, d251181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248696, d251181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d246245 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248697 q = 1) (hb : d251182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248697, d251182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248697, d251182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248698 q = 1) (hb : d251183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248698, d251183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248698, d251183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248699 q = 1) (hb : d251184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248699, d251184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248699, d251184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248700 q = 1) (hb : d251185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248700, d251185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248700, d251185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62841 (p : Pattern) (ha : d250752 p = 1) (hb : d251192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248696 q = 1) (hb : d251181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248696, d251181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248696, d251181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246245 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248697 q = 1) (hb : d251182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248697, d251182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248697, d251182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248698 q = 1) (hb : d251190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248698, d251190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248698, d251190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248699 q = 1) (hb : d251191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248699, d251191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248699, d251191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250752 q = 1) (hb : d251192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250752, d251192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250752, d251192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62842 (p : Pattern) (ha : d250763 p = 1) (hb : d251202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246294 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d250758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d250759 q = 1) (hb : d251198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d250759, d251198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250759, d251198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246319 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250760 q = 1) (hb : d251199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d250760, d251199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250760, d251199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250761 q = 1) (hb : d251200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d250761, d251200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250761, d251200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250762 q = 1) (hb : d251201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d250762, d251201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250762, d251201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250763 q = 1) (hb : d251202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250763, d251202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250763, d251202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62843 (p : Pattern) (ha : d250769 p = 1) (hb : d251208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246169 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248701 q = 1) (hb : d251186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248701, d251186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62839 q ha hb
    | true =>
      simp only [d248701, d251186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62840 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246252 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248702 q = 1) (hb : d251187 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248702, d251187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248702, d251187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250750 q = 1) (hb : d251188 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250750, d251188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250750, d251188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250751 q = 1) (hb : d251189 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250751, d251189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250751, d251189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250753 q = 1) (hb : d251193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250753, d251193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250753, d251193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62841 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d117333 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d250754 q = 1) (hb : d251194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250754, d251194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d250754, d251194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d250755 q = 1) (hb : d251195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250755, d251195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d250755, d251195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d250756 q = 1) (hb : d251196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250756, d251196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d250756, d251196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d250757 q = 1) (hb : d251197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250757, d251197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d250757, d251197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d250764 q = 1) (hb : d251203 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250764, d251203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250764, d251203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62842 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d117438 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d250765 q = 1) (hb : d251204 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250765, d251204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d250765, d251204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d250766 q = 1) (hb : d251205 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250766, d251205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d250766, d251205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d250767 q = 1) (hb : d251206 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250767, d251206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d250767, d251206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d250768 q = 1) (hb : d251207 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250768, d251207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d250768, d251207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d250769 q = 1) (hb : d251208 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d250769, d251208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d250769, d251208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62844 (p : Pattern) (ha : d250775 p = 1) (hb : d251214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250770 q = 1) (hb : d251209 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d250770, d251209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250770, d251209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62843 q ha hb
  have h2 (q : Pattern) (ha : d250771 q = 1) (hb : d251210 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d250771, d251210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250771, d251210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d250772 q = 1) (hb : d251211 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d250772, d251211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250772, d251211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d250773 q = 1) (hb : d251212 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d250773, d251212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250773, d251212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d250774 q = 1) (hb : d251213 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d250774, d251213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250774, d251213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250775 q = 1) (hb : d251214 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d250775, d251214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250775, d251214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62845 (p : Pattern) (ha : d248903 p = 1) (hb : d251221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246403 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246412 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d246430 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d248898 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248899 q = 1) (hb : d251217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248899, d251217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248899, d251217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d246485 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248900 q = 1) (hb : d251218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248900, d251218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248900, d251218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248901 q = 1) (hb : d251219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248901, d251219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248901, d251219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248902 q = 1) (hb : d251220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248902, d251220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248902, d251220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248903 q = 1) (hb : d251221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248903, d251221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248903, d251221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62846 (p : Pattern) (ha : d248913 p = 1) (hb : d251226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246430 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d248898 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d248899 q = 1) (hb : d251217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248899, d251217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248899, d251217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d246485 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d248900 q = 1) (hb : d251218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248900, d251218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248900, d251218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248901 q = 1) (hb : d251219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248901, d251219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248901, d251219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248902 q = 1) (hb : d251220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248902, d251220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248902, d251220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d246495 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d246500 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d246502 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d248908 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d248909 q = 1) (hb : d251222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248909, d251222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248909, d251222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d246509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248910 q = 1) (hb : d251223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248910, d251223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248910, d251223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248911 q = 1) (hb : d251224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248911, d251224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248911, d251224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248912 q = 1) (hb : d251225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248912, d251225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248912, d251225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248913 q = 1) (hb : d251226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248913, d251226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248913, d251226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62847 (p : Pattern) (ha : d250780 p = 1) (hb : d251233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246502 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248909 q = 1) (hb : d251222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248909, d251222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248909, d251222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246509 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d248910 q = 1) (hb : d251223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248910, d251223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248910, d251223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248911 q = 1) (hb : d251231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248911, d251231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248911, d251231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248912 q = 1) (hb : d251232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248912, d251232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d248912, d251232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250780 q = 1) (hb : d251233 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250780, d251233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250780, d251233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62848 (p : Pattern) (ha : d250791 p = 1) (hb : d251243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d250786 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d250787 q = 1) (hb : d251239 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d250787, d251239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250787, d251239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246648 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250788 q = 1) (hb : d251240 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d250788, d251240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250788, d251240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250789 q = 1) (hb : d251241 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d250789, d251241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250789, d251241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250790 q = 1) (hb : d251242 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d250790, d251242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250790, d251242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250791 q = 1) (hb : d251243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250791, d251243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250791, d251243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62849 (p : Pattern) (ha : d250797 p = 1) (hb : d251249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248914 q = 1) (hb : d251227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248914, d251227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62845 q ha hb
    | true =>
      simp only [d248914, d251227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62846 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248915 q = 1) (hb : d251228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248915, d251228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248915, d251228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250778 q = 1) (hb : d251229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250778, d251229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250778, d251229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250779 q = 1) (hb : d251230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250779, d251230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250779, d251230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250781 q = 1) (hb : d251234 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250781, d251234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250781, d251234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62847 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d246536 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d250782 q = 1) (hb : d251235 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250782, d251235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d250782, d251235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d250783 q = 1) (hb : d251236 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250783, d251236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d250783, d251236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d250784 q = 1) (hb : d251237 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250784, d251237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d250784, d251237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d250785 q = 1) (hb : d251238 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250785, d251238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d250785, d251238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d250792 q = 1) (hb : d251244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250792, d251244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250792, d251244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62848 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d246664 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d250793 q = 1) (hb : d251245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250793, d251245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d250793, d251245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d250794 q = 1) (hb : d251246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250794, d251246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d250794, d251246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d250795 q = 1) (hb : d251247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250795, d251247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d250795, d251247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d250796 q = 1) (hb : d251248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250796, d251248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d250796, d251248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d250797 q = 1) (hb : d251249 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d250797, d251249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d250797, d251249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62850 (p : Pattern) (ha : d250803 p = 1) (hb : d251255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250798 q = 1) (hb : d251250 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d250798, d251250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250798, d251250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62849 q ha hb
  have h2 (q : Pattern) (ha : d250799 q = 1) (hb : d251251 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d250799, d251251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250799, d251251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d250800 q = 1) (hb : d251252 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d250800, d251252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250800, d251252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d250801 q = 1) (hb : d251253 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d250801, d251253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250801, d251253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d250802 q = 1) (hb : d251254 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d250802, d251254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250802, d251254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250803 q = 1) (hb : d251255 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d250803, d251255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250803, d251255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62851 (p : Pattern) (ha : d249179 p = 1) (hb : d251263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d246771 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d249174 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d249175 q = 1) (hb : d251259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249175, d251259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d249175, d251259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d246826 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d249176 q = 1) (hb : d251260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249176, d251260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d249176, d251260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d249177 q = 1) (hb : d251261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249177, d251261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d249177, d251261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d249178 q = 1) (hb : d251262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249178, d251262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249178, d251262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d249179 q = 1) (hb : d251263 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d249179, d251263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249179, d251263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62852 (p : Pattern) (ha : d249189 p = 1) (hb : d251268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246744 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d249174 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d249175 q = 1) (hb : d251259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249175, d251259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d249175, d251259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d246826 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d249176 q = 1) (hb : d251260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249176, d251260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d249176, d251260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d249177 q = 1) (hb : d251261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249177, d251261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249177, d251261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d249178 q = 1) (hb : d251262 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249178, d251262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249178, d251262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d246836 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d246841 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d246843 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d249184 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d249185 q = 1) (hb : d251264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249185, d251264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d249185, d251264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d246850 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d249186 q = 1) (hb : d251265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249186, d251265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249186, d251265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d249187 q = 1) (hb : d251266 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249187, d251266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d249187, d251266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d249188 q = 1) (hb : d251267 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249188, d251267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d249188, d251267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d249189 q = 1) (hb : d251268 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d249189, d251268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249189, d251268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62853 (p : Pattern) (ha : d250809 p = 1) (hb : d251275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d249184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d249185 q = 1) (hb : d251264 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249185, d251264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249185, d251264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246850 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d249186 q = 1) (hb : d251265 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249186, d251265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d249186, d251265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d249187 q = 1) (hb : d251273 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249187, d251273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249187, d251273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d249188 q = 1) (hb : d251274 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249188, d251274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249188, d251274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250809 q = 1) (hb : d251275 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250809, d251275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250809, d251275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62854 (p : Pattern) (ha : d250820 p = 1) (hb : d251285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d246934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d250815 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d250816 q = 1) (hb : d251281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d250816, d251281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250816, d251281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d246989 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250817 q = 1) (hb : d251282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d250817, d251282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250817, d251282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250818 q = 1) (hb : d251283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d250818, d251283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250818, d251283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250819 q = 1) (hb : d251284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d250819, d251284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250819, d251284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250820 q = 1) (hb : d251285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250820, d251285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250820, d251285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62855 (p : Pattern) (ha : d250826 p = 1) (hb : d251291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d246736 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d249190 q = 1) (hb : d251269 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d249190, d251269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62851 q ha hb
    | true =>
      simp only [d249190, d251269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62852 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d246868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d249191 q = 1) (hb : d251270 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d249191, d251270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249191, d251270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250807 q = 1) (hb : d251271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250807, d251271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250807, d251271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250808 q = 1) (hb : d251272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250808, d251272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250808, d251272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250810 q = 1) (hb : d251276 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250810, d251276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250810, d251276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62853 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d246877 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d250811 q = 1) (hb : d251277 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250811, d251277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d250811, d251277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d250812 q = 1) (hb : d251278 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250812, d251278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d250812, d251278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d250813 q = 1) (hb : d251279 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250813, d251279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d250813, d251279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d250814 q = 1) (hb : d251280 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250814, d251280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d250814, d251280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d250821 q = 1) (hb : d251286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250821, d251286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250821, d251286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62854 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247005 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d250822 q = 1) (hb : d251287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250822, d251287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d250822, d251287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d250823 q = 1) (hb : d251288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250823, d251288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d250823, d251288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d250824 q = 1) (hb : d251289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250824, d251289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d250824, d251289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d250825 q = 1) (hb : d251290 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250825, d251290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d250825, d251290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d250826 q = 1) (hb : d251291 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d250826, d251291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d250826, d251291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62856 (p : Pattern) (ha : d250832 p = 1) (hb : d251297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250827 q = 1) (hb : d251292 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d250827, d251292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250827, d251292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62855 q ha hb
  have h2 (q : Pattern) (ha : d250828 q = 1) (hb : d251293 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d250828, d251293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250828, d251293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d250829 q = 1) (hb : d251294 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d250829, d251294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250829, d251294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d250830 q = 1) (hb : d251295 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d250830, d251295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250830, d251295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d250831 q = 1) (hb : d251296 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d250831, d251296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250831, d251296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250832 q = 1) (hb : d251297 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d250832, d251297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250832, d251297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62857 (p : Pattern) (ha : d249450 p = 1) (hb : d251306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d247109 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d249445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d249446 q = 1) (hb : d251302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249446, d251302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d249446, d251302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d247164 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d249447 q = 1) (hb : d251303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249447, d251303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d249447, d251303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d249448 q = 1) (hb : d251304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249448, d251304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d249448, d251304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d249449 q = 1) (hb : d251305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249449, d251305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249449, d251305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d249450 q = 1) (hb : d251306 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d249450, d251306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249450, d251306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62858 (p : Pattern) (ha : d249460 p = 1) (hb : d251311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d249445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d249446 q = 1) (hb : d251302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249446, d251302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d249446, d251302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d247164 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d249447 q = 1) (hb : d251303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249447, d251303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d249447, d251303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d249448 q = 1) (hb : d251304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249448, d251304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249448, d251304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d249449 q = 1) (hb : d251305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249449, d251305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249449, d251305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247174 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247179 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d247181 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d249455 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d249456 q = 1) (hb : d251307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249456, d251307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d249456, d251307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247188 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d249457 q = 1) (hb : d251308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249457, d251308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249457, d251308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d249458 q = 1) (hb : d251309 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249458, d251309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d249458, d251309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d249459 q = 1) (hb : d251310 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249459, d251310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d249459, d251310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d249460 q = 1) (hb : d251311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d249460, d251311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249460, d251311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62859 (p : Pattern) (ha : d250839 p = 1) (hb : d251318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d249455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d249456 q = 1) (hb : d251307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d249456, d251307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249456, d251307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d249457 q = 1) (hb : d251308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d249457, d251308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d249457, d251308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d249458 q = 1) (hb : d251316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d249458, d251316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249458, d251316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d249459 q = 1) (hb : d251317 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d249459, d251317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d249459, d251317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250839 q = 1) (hb : d251318 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250839, d251318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250839, d251318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62860 (p : Pattern) (ha : d250850 p = 1) (hb : d251328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d247268 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d250845 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d250846 q = 1) (hb : d251324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d250846, d251324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250846, d251324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d247323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250847 q = 1) (hb : d251325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d250847, d251325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250847, d251325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250848 q = 1) (hb : d251326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d250848, d251326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250848, d251326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250849 q = 1) (hb : d251327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d250849, d251327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250849, d251327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d250850 q = 1) (hb : d251328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d250850, d251328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250850, d251328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62861 (p : Pattern) (ha : d250856 p = 1) (hb : d251334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d247078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d249461 q = 1) (hb : d251312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d249461, d251312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62857 q ha hb
    | true =>
      simp only [d249461, d251312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62858 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247206 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d249462 q = 1) (hb : d251313 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d249462, d251313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d249462, d251313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d250837 q = 1) (hb : d251314 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250837, d251314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250837, d251314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250838 q = 1) (hb : d251315 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250838, d251315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250838, d251315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250840 q = 1) (hb : d251319 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250840, d251319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250840, d251319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62859 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d247215 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d250841 q = 1) (hb : d251320 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250841, d251320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d250841, d251320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d250842 q = 1) (hb : d251321 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250842, d251321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d250842, d251321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d250843 q = 1) (hb : d251322 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250843, d251322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d250843, d251322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d250844 q = 1) (hb : d251323 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250844, d251323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d250844, d251323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d250851 q = 1) (hb : d251329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d250851, d251329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250851, d251329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62860 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247339 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d250852 q = 1) (hb : d251330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d250852, d251330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d250852, d251330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d250853 q = 1) (hb : d251331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d250853, d251331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d250853, d251331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d250854 q = 1) (hb : d251332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d250854, d251332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d250854, d251332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d250855 q = 1) (hb : d251333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d250855, d251333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d250855, d251333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d250856 q = 1) (hb : d251334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d250856, d251334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d250856, d251334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62862 (p : Pattern) (ha : d250862 p = 1) (hb : d251340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250857 q = 1) (hb : d251335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d250857, d251335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250857, d251335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62861 q ha hb
  have h2 (q : Pattern) (ha : d250858 q = 1) (hb : d251336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d250858, d251336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250858, d251336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d250859 q = 1) (hb : d251337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d250859, d251337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250859, d251337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d250860 q = 1) (hb : d251338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d250860, d251338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250860, d251338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d250861 q = 1) (hb : d251339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d250861, d251339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250861, d251339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250862 q = 1) (hb : d251340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d250862, d251340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250862, d251340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62863 (p : Pattern) (ha : d250868 p = 1) (hb : d251346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d158074 q = 1) (hb : d251175 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158074, d251175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62832 q ha hb
    | true =>
      simp only [d158074, d251175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62838 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d250776 q = 1) (hb : d251215 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d250776, d251215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250776, d251215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62844 q ha hb
  have h3 (q : Pattern) (ha : d250777 q = 1) (hb : d251216 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d250777, d251216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d250777, d251216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d250804 q = 1) (hb : d251256 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d250804, d251256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250804, d251256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62850 q ha hb
  have h5 (q : Pattern) (ha : d250805 q = 1) (hb : d251257 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d250805, d251257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250805, d251257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d250806 q = 1) (hb : d251258 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d250806, d251258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250806, d251258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d250833 q = 1) (hb : d251298 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d250833, d251298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250833, d251298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62856 q ha hb
  have h8 (q : Pattern) (ha : d250834 q = 1) (hb : d251299 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d250834, d251299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250834, d251299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d250835 q = 1) (hb : d251300 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d250835, d251300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250835, d251300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d250836 q = 1) (hb : d251301 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d250836, d251301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d250836, d251301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d250863 q = 1) (hb : d251341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d250863, d251341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250863, d251341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62862 q ha hb
  have h12 (q : Pattern) (ha : d250864 q = 1) (hb : d251342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d250864, d251342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250864, d251342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d250865 q = 1) (hb : d251343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d250865, d251343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250865, d251343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d250866 q = 1) (hb : d251344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d250866, d251344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250866, d251344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d250867 q = 1) (hb : d251345 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d250867, d251345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d250867, d251345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d250868 q = 1) (hb : d251346 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d250868, d251346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d250868, d251346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro62864 (p : Pattern) (ha : d250874 p = 1) (hb : d251352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250869 q = 1) (hb : d251347 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d250869, d251347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62863 q ha hb
    | true =>
      simp only [d250869, d251347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250870 q = 1) (hb : d251348 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d250870, d251348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250870, d251348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250871 q = 1) (hb : d251349 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d250871, d251349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250871, d251349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250872 q = 1) (hb : d251350 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d250872, d251350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250872, d251350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250873 q = 1) (hb : d251351 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d250873, d251351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250873, d251351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250874 q = 1) (hb : d251352 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d250874, d251352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250874, d251352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62865 (p : Pattern) (ha : d250880 p = 1) (hb : d251358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250875 q = 1) (hb : d251353 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d250875, d251353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62864 q ha hb
    | true =>
      simp only [d250875, d251353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250876 q = 1) (hb : d251354 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d250876, d251354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250876, d251354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250877 q = 1) (hb : d251355 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d250877, d251355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250877, d251355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250878 q = 1) (hb : d251356 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d250878, d251356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250878, d251356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250879 q = 1) (hb : d251357 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d250879, d251357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250879, d251357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250880 q = 1) (hb : d251358 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d250880, d251358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250880, d251358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62866 (p : Pattern) (ha : d250886 p = 1) (hb : d251364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250881 q = 1) (hb : d251359 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d250881, d251359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62865 q ha hb
    | true =>
      simp only [d250881, d251359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250882 q = 1) (hb : d251360 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d250882, d251360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250882, d251360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250883 q = 1) (hb : d251361 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d250883, d251361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250883, d251361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250884 q = 1) (hb : d251362 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d250884, d251362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250884, d251362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250885 q = 1) (hb : d251363 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d250885, d251363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250885, d251363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250886 q = 1) (hb : d251364 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d250886, d251364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250886, d251364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62867 (p : Pattern) (ha : d250892 p = 1) (hb : d251370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250887 q = 1) (hb : d251365 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d250887, d251365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62866 q ha hb
    | true =>
      simp only [d250887, d251365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250888 q = 1) (hb : d251366 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d250888, d251366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250888, d251366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250889 q = 1) (hb : d251367 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d250889, d251367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250889, d251367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250890 q = 1) (hb : d251368 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d250890, d251368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250890, d251368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250891 q = 1) (hb : d251369 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d250891, d251369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250891, d251369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250892 q = 1) (hb : d251370 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d250892, d251370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250892, d251370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62868 (p : Pattern) (ha : d250898 p = 1) (hb : d251376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250893 q = 1) (hb : d251371 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d250893, d251371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62867 q ha hb
    | true =>
      simp only [d250893, d251371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250894 q = 1) (hb : d251372 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d250894, d251372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250894, d251372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250895 q = 1) (hb : d251373 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d250895, d251373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250895, d251373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250896 q = 1) (hb : d251374 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d250896, d251374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250896, d251374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250897 q = 1) (hb : d251375 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d250897, d251375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250897, d251375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250898 q = 1) (hb : d251376 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d250898, d251376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250898, d251376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62869 (p : Pattern) (ha : d250904 p = 1) (hb : d251382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250899 q = 1) (hb : d251377 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d250899, d251377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62868 q ha hb
    | true =>
      simp only [d250899, d251377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250900 q = 1) (hb : d251378 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d250900, d251378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250900, d251378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250901 q = 1) (hb : d251379 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d250901, d251379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250901, d251379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250902 q = 1) (hb : d251380 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d250902, d251380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250902, d251380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250903 q = 1) (hb : d251381 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d250903, d251381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250903, d251381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250904 q = 1) (hb : d251382 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d250904, d251382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250904, d251382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62870 (p : Pattern) (ha : d250910 p = 1) (hb : d251388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d250905 q = 1) (hb : d251383 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d250905, d251383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62869 q ha hb
    | true =>
      simp only [d250905, d251383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d250906 q = 1) (hb : d251384 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d250906, d251384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d250906, d251384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d250907 q = 1) (hb : d251385 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d250907, d251385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d250907, d251385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d250908 q = 1) (hb : d251386 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d250908, d251386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d250908, d251386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d250909 q = 1) (hb : d251387 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d250909, d251387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d250909, d251387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d250910 q = 1) (hb : d251388 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d250910, d251388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d250910, d251388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62871 (p : Pattern) (ha : d25104 p = 1) (hb : d251389 p = 1) : d251392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d251389 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25102 q = 1) (hb : d251389 q = 1) : d251390 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25103 q = 1) (hb : d251389 q = 1) : d251391 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d251389 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25104 q = 1) (hb : d251389 q = 1) : d251392 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d251392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25104, d251392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62872 (p : Pattern) (ha : d25110 p = 1) (hb : d251389 p = 1) : d251398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
    | true =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d251389 q = 1) : d251395 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d251389 q = 1) : d251396 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d251389 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25109 q = 1) (hb : d251389 q = 1) : d251397 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d251397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d251397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d251389 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25110 q = 1) (hb : d251389 q = 1) : d251398 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d251398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25110, d251398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62873 (p : Pattern) (ha : d25116 p = 1) (hb : d251389 p = 1) : d251404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
    | true =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d251389 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25114 q = 1) (hb : d251389 q = 1) : d251402 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25114, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d251389 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25115 q = 1) (hb : d251389 q = 1) : d251403 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d251403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25115, d251403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25116 q = 1) (hb : d251389 q = 1) : d251404 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d251404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25116, d251404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro62874 (p : Pattern) (ha : d25122 p = 1) (hb : d251389 p = 1) : d251410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d251389 q = 1) : d251409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25122 q = 1) (hb : d251389 q = 1) : d251410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d251410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d251410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62875 (p : Pattern) (ha : d201977 p = 1) (hb : d251389 p = 1) : d251416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d251389 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d251389 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25123 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
    | true =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d201973 q = 1) (hb : d251389 q = 1) : d251412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201973, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d251389 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201974 q = 1) (hb : d251389 q = 1) : d251413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201975 q = 1) (hb : d251389 q = 1) : d251414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201975, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201976 q = 1) (hb : d251389 q = 1) : d251415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201976, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d201977 q = 1) (hb : d251389 q = 1) : d251416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d251416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201977, d251416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62876 (p : Pattern) (ha : d25129 p = 1) (hb : d251389 p = 1) : d251417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25121 q = 1) (hb : d251389 q = 1) : d251409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25121, d251409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25129 q = 1) (hb : d251389 q = 1) : d251417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d251417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25129, d251417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62877 (p : Pattern) (ha : d201982 p = 1) (hb : d251389 p = 1) : d251423 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d251389 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d251389 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25123 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
    | true =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201973 q = 1) (hb : d251389 q = 1) : d251412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201973, d251412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d251389 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d201974 q = 1) (hb : d251389 q = 1) : d251413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d201974, d251413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201975 q = 1) (hb : d251389 q = 1) : d251414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201975, d251414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d201976 q = 1) (hb : d251389 q = 1) : d251415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201976, d251415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d251389 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d251389 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25130 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
    | true =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d201978 q = 1) (hb : d251389 q = 1) : d251419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201978, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d251389 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d201979 q = 1) (hb : d251389 q = 1) : d251420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201979, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d201980 q = 1) (hb : d251389 q = 1) : d251421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d251421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201980, d251421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d201981 q = 1) (hb : d251389 q = 1) : d251422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d251422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201981, d251422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d201982 q = 1) (hb : d251389 q = 1) : d251423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d251423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201982, d251423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62878 (p : Pattern) (ha : d201989 p = 1) (hb : d251389 p = 1) : d251430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
    | true =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201978 q = 1) (hb : d251389 q = 1) : d251419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201978, d251419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d251389 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201979 q = 1) (hb : d251389 q = 1) : d251420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201979, d251420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201987 q = 1) (hb : d251389 q = 1) : d251428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d251428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201987, d251428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201988 q = 1) (hb : d251389 q = 1) : d251429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d251429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201988, d251429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201989 q = 1) (hb : d251389 q = 1) : d251430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d251430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201989, d251430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62879 (p : Pattern) (ha : d25153 p = 1) (hb : d251389 p = 1) : d251441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d251389 q = 1) : d251436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
    | true =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d251389 q = 1) : d251437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d251389 q = 1) : d251438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d251389 q = 1) : d251439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d251389 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25152 q = 1) (hb : d251389 q = 1) : d251440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d251440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d251440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d251389 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25153 q = 1) (hb : d251389 q = 1) : d251441 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d251441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25153, d251441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62880 (p : Pattern) (ha : d25159 p = 1) (hb : d251389 p = 1) : d251447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
    | true =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d251389 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25157 q = 1) (hb : d251389 q = 1) : d251445 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25157, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d251389 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25158 q = 1) (hb : d251389 q = 1) : d251446 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d251446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25158, d251446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25159 q = 1) (hb : d251389 q = 1) : d251447 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d251447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25159, d251447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro62881 (p : Pattern) (ha : d25165 p = 1) (hb : d251389 p = 1) : d251453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d251389 q = 1) : d251448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62880 q ha hb
    | true =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d251389 q = 1) : d251449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d251389 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25162 q = 1) (hb : d251389 q = 1) : d251450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d251450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d251450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25163 q = 1) (hb : d251389 q = 1) : d251451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d251451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25163, d251451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25164 q = 1) (hb : d251389 q = 1) : d251452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d251452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25164, d251452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25165 q = 1) (hb : d251389 q = 1) : d251453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d251453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25165, d251453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62882 (p : Pattern) (ha : d201999 p = 1) (hb : d251389 p = 1) : d251459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d251389 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d251389 q = 1) : d251454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62881 q ha hb
    | true =>
      simp only [d25166, d251454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d201995 q = 1) (hb : d251389 q = 1) : d251455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d251455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201995, d251455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d251389 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201996 q = 1) (hb : d251389 q = 1) : d251456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d251456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201996, d251456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201997 q = 1) (hb : d251389 q = 1) : d251457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d251457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201997, d251457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201998 q = 1) (hb : d251389 q = 1) : d251458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d251458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201998, d251458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d201999 q = 1) (hb : d251389 q = 1) : d251459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d251459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201999, d251459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62883 (p : Pattern) (ha : d202005 p = 1) (hb : d251389 p = 1) : d251465 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d251389 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d201983 q = 1) (hb : d251389 q = 1) : d251424 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d251424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62875 q ha hb
    | true =>
      simp only [d201983, d251424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62877 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d251389 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d201984 q = 1) (hb : d251389 q = 1) : d251425 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d251425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201984, d251425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d201985 q = 1) (hb : d251389 q = 1) : d251426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d251426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d201985, d251426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d201986 q = 1) (hb : d251389 q = 1) : d251427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d251427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201986, d251427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d201990 q = 1) (hb : d251389 q = 1) : d251431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d251431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d201990, d251431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62878 q ha hb
  have h8 (q : Pattern) (ha : d201991 q = 1) (hb : d251389 q = 1) : d251432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d251432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d201991, d251432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d201992 q = 1) (hb : d251389 q = 1) : d251433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d251433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201992, d251433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d201993 q = 1) (hb : d251389 q = 1) : d251434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d251434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201993, d251434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d201994 q = 1) (hb : d251389 q = 1) : d251435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d251435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201994, d251435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202000 q = 1) (hb : d251389 q = 1) : d251460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d251460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202000, d251460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62882 q ha hb
  have h13 (q : Pattern) (ha : d202001 q = 1) (hb : d251389 q = 1) : d251461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d251461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202001, d251461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d202002 q = 1) (hb : d251389 q = 1) : d251462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d251462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202002, d251462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d202003 q = 1) (hb : d251389 q = 1) : d251463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d251463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202003, d251463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d202004 q = 1) (hb : d251389 q = 1) : d251464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d251464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202004, d251464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202005 q = 1) (hb : d251389 q = 1) : d251465 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d251465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202005, d251465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62884 (p : Pattern) (ha : d25187 p = 1) (hb : d251389 p = 1) : d251475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
    | true =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d251389 q = 1) : d251471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d251389 q = 1) : d251472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d251389 q = 1) : d251473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d251389 q = 1) : d251474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25187 q = 1) (hb : d251389 q = 1) : d251475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d251475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62885 (p : Pattern) (ha : d25194 p = 1) (hb : d251389 p = 1) : d251482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
    | true =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d251389 q = 1) : d251471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d251389 q = 1) : d251472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d251389 q = 1) : d251473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d251389 q = 1) : d251474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d251389 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25130 q = 1) (hb : d251389 q = 1) : d251418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
    | true =>
      simp only [d25130, d251418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25190 q = 1) (hb : d251389 q = 1) : d251478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d251478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25191 q = 1) (hb : d251389 q = 1) : d251479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25191, d251479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25192 q = 1) (hb : d251389 q = 1) : d251480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d251480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25193 q = 1) (hb : d251389 q = 1) : d251481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d251481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25194 q = 1) (hb : d251389 q = 1) : d251482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25194, d251482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro62886 (p : Pattern) (ha : d25296 p = 1) (hb : d251389 p = 1) : d251560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d251389 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25123 q = 1) (hb : d251389 q = 1) : d251411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
    | true =>
      simp only [d25123, d251411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25183 q = 1) (hb : d251389 q = 1) : d251471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d251471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25184 q = 1) (hb : d251389 q = 1) : d251472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25184, d251472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25185 q = 1) (hb : d251389 q = 1) : d251473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d251473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25186 q = 1) (hb : d251389 q = 1) : d251474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d251474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d251389 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25296 q = 1) (hb : d251389 q = 1) : d251560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d251560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25296, d251560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62887 (p : Pattern) (ha : d25199 p = 1) (hb : d251389 p = 1) : d251487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d251389 q = 1) : d251486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d251486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d251486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25199 q = 1) (hb : d251389 q = 1) : d251487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d251487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d251487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62888 (p : Pattern) (ha : d25206 p = 1) (hb : d251389 p = 1) : d251494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d251389 q = 1) : d251492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d251492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d251492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d251389 q = 1) : d251493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d251493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d251493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25206 q = 1) (hb : d251389 q = 1) : d251494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d251494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d251494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62889 (p : Pattern) (ha : d25213 p = 1) (hb : d251389 p = 1) : d251501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25211 q = 1) (hb : d251389 q = 1) : d251499 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25211, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25212 q = 1) (hb : d251389 q = 1) : d251500 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25212, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d251389 q = 1) : d21 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25102 q = 1) (hb : d251389 q = 1) : d251390 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25103 q = 1) (hb : d251389 q = 1) : d251391 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d25213 q = 1) (hb : d251389 q = 1) : d251501 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d251501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25213, d251501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro62890 (p : Pattern) (ha : d25221 p = 1) (hb : d251389 p = 1) : d251509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25219 q = 1) (hb : d251389 q = 1) : d251507 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25220 q = 1) (hb : d251389 q = 1) : d251508 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d251389 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d25221 q = 1) (hb : d251389 q = 1) : d251509 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, d251509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25221, d251509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62891 (p : Pattern) (ha : d25227 p = 1) (hb : d251389 p = 1) : d251515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d251389 q = 1) : d251502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
    | true =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d251389 q = 1) : d251503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d251389 q = 1) : d251504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d251504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d251504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d251389 q = 1) : d251505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d251505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d251505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
    | true =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d251389 q = 1) : d251395 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d251395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d251389 q = 1) : d251396 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d251396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d251389 q = 1) : d251506 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d251506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d251506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25224 q = 1) (hb : d251389 q = 1) : d251512 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25225 q = 1) (hb : d251389 q = 1) : d251513 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d251389 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25226 q = 1) (hb : d251389 q = 1) : d251514 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d251514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25226, d251514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25227 q = 1) (hb : d251389 q = 1) : d251515 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d251515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d251515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62892 (p : Pattern) (ha : d25233 p = 1) (hb : d251389 p = 1) : d251521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d251389 q = 1) : d251516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62891 q ha hb
    | true =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d251389 q = 1) : d251517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d251389 q = 1) : d251518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
    | true =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d251389 q = 1) : d251519 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d251389 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25114 q = 1) (hb : d251389 q = 1) : d251402 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25114, d251402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25232 q = 1) (hb : d251389 q = 1) : d251520 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d251520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25232, d251520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25233 q = 1) (hb : d251389 q = 1) : d251521 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d251521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25233, d251521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro62893 (p : Pattern) (ha : d25239 p = 1) (hb : d251389 p = 1) : d251527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d251389 q = 1) : d251522 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d251522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62892 q ha hb
    | true =>
      simp only [d25234, d251522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d251389 q = 1) : d251523 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d251523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d251523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d251389 q = 1) : d251524 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d251524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d251524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d251389 q = 1) : d251525 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d251525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d251525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d251389 q = 1) : d251526 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d251526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d251526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d251389 q = 1) : d251527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d251527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d251527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62894 (p : Pattern) (ha : d25267 p = 1) (hb : d251389 p = 1) : d251533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d251389 q = 1) : d251530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d251530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d251530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d251389 q = 1) : d251531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d251531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d251531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d251389 q = 1) : d251532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d251532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d251532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d251389 q = 1) : d251533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d251533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d251533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62895 (p : Pattern) (ha : d202015 p = 1) (hb : d251389 p = 1) : d251539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d251389 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d251389 q = 1) : d251488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d251488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62887 q ha hb
    | true =>
      simp only [d25200, d251488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d251389 q = 1) : d251489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d251489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d251489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d251389 q = 1) : d251490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d251490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d251490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d251389 q = 1) : d251491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d251491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d251491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d251389 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d251389 q = 1) : d251495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d251495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62888 q ha hb
    | true =>
      simp only [d25207, d251495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d251389 q = 1) : d251496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d251496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d251496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d251389 q = 1) : d251497 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d251497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d251497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d251389 q = 1) : d251528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d251528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62893 q ha hb
    | true =>
      simp only [d25240, d251528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
  have h11 (q : Pattern) (ha : d202011 q = 1) (hb : d251389 q = 1) : d251529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d251529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202011, d251529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d251389 q = 1) : d251534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d251534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62894 q ha hb
    | true =>
      simp only [d25268, d251534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d251389 q = 1) : d251535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d251535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d251535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d202012 q = 1) (hb : d251389 q = 1) : d251536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d251536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d251536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202013 q = 1) (hb : d251389 q = 1) : d251537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d251537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202013, d251537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202014 q = 1) (hb : d251389 q = 1) : d251538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d251538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202014, d251538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202015 q = 1) (hb : d251389 q = 1) : d251539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d251539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202015, d251539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62896 (p : Pattern) (ha : d25274 p = 1) (hb : d251389 p = 1) : d251540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25120 q = 1) (hb : d251389 q = 1) : d251408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25120, d251408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25198 q = 1) (hb : d251389 q = 1) : d251486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d251486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d251486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25274 q = 1) (hb : d251389 q = 1) : d251540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d251540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25274, d251540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62897 (p : Pattern) (ha : d25279 p = 1) (hb : d251389 p = 1) : d251545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d251389 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25119 q = 1) (hb : d251389 q = 1) : d251407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d251407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25204 q = 1) (hb : d251389 q = 1) : d251492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d251492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d251492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25205 q = 1) (hb : d251389 q = 1) : d251493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d251493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25205, d251493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25279 q = 1) (hb : d251389 q = 1) : d251545 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d251545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25279, d251545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62898 (p : Pattern) (ha : d25283 p = 1) (hb : d251389 p = 1) : d251549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d251389 q = 1) : d251522 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d251522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62892 q ha hb
    | true =>
      simp only [d25234, d251522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d251389 q = 1) : d251523 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d251523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d251523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d251389 q = 1) : d251524 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d251524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d251524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d251389 q = 1) : d251525 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d251525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d251525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d251389 q = 1) : d251526 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d251526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d251526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d251389 q = 1) : d251549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d251549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d251549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62899 (p : Pattern) (ha : d25288 p = 1) (hb : d251389 p = 1) : d251552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d251389 q = 1) : d251405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62873 q ha hb
    | true =>
      simp only [d25117, d251405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d251389 q = 1) : d251406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d251406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d251389 q = 1) : d251530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d251530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d251530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d251389 q = 1) : d251531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d251531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d251531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d251389 q = 1) : d251532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d251532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d251532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d251389 q = 1) : d251552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d251552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d251552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62900 (p : Pattern) (ha : d202020 p = 1) (hb : d251389 p = 1) : d251558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d251389 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25200 q = 1) (hb : d251389 q = 1) : d251488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d251488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62887 q ha hb
    | true =>
      simp only [d25200, d251488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25201 q = 1) (hb : d251389 q = 1) : d251489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d251489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d251489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25202 q = 1) (hb : d251389 q = 1) : d251490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d251490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25202, d251490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25203 q = 1) (hb : d251389 q = 1) : d251491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d251491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d251491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d251389 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25207 q = 1) (hb : d251389 q = 1) : d251495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d251495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62888 q ha hb
    | true =>
      simp only [d25207, d251495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25208 q = 1) (hb : d251389 q = 1) : d251496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d251496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d251496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25209 q = 1) (hb : d251389 q = 1) : d251497 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d251497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25209, d251497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25240 q = 1) (hb : d251389 q = 1) : d251528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d251528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62893 q ha hb
    | true =>
      simp only [d25240, d251528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62874 q ha hb
  have h11 (q : Pattern) (ha : d202011 q = 1) (hb : d251389 q = 1) : d251529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d251529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202011, d251529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25268 q = 1) (hb : d251389 q = 1) : d251534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d251534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62894 q ha hb
    | true =>
      simp only [d25268, d251534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25269 q = 1) (hb : d251389 q = 1) : d251535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d251535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25269, d251535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d202012 q = 1) (hb : d251389 q = 1) : d251536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d251536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202012, d251536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202013 q = 1) (hb : d251389 q = 1) : d251537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d251537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202013, d251537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202014 q = 1) (hb : d251389 q = 1) : d251538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d251538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202014, d251538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d251389 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d25275 q = 1) (hb : d251389 q = 1) : d251541 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d251541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62896 q ha hb
    | true =>
      simp only [d25275, d251541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25276 q = 1) (hb : d251389 q = 1) : d251542 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d251542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d251542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d25277 q = 1) (hb : d251389 q = 1) : d251543 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d251543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25277, d251543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d25278 q = 1) (hb : d251389 q = 1) : d251544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d251544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d251544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d251389 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d25280 q = 1) (hb : d251389 q = 1) : d251546 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d251546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62897 q ha hb
    | true =>
      simp only [d25280, d251546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d25281 q = 1) (hb : d251389 q = 1) : d251547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d251547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d251547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25282 q = 1) (hb : d251389 q = 1) : d251548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d251548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25282, d251548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25284 q = 1) (hb : d251389 q = 1) : d251550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d251550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62898 q ha hb
    | true =>
      simp only [d25284, d251550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
  have h27 (q : Pattern) (ha : d202016 q = 1) (hb : d251389 q = 1) : d251551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d251551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d202016, d251551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d25289 q = 1) (hb : d251389 q = 1) : d251553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d251553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62899 q ha hb
    | true =>
      simp only [d25289, d251553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d25290 q = 1) (hb : d251389 q = 1) : d251554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d251554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d25290, d251554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d202017 q = 1) (hb : d251389 q = 1) : d251555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d251555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d202017, d251555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d202018 q = 1) (hb : d251389 q = 1) : d251556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d251556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d202018, d251556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d202019 q = 1) (hb : d251389 q = 1) : d251557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d251557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202019, d251557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d202020 q = 1) (hb : d251389 q = 1) : d251558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d251558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202020, d251558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro62901 (p : Pattern) (ha : d202027 p = 1) (hb : d251389 p = 1) : d251567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d251389 q = 1) : d251550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d251550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62898 q ha hb
    | true =>
      simp only [d25284, d251550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62876 q ha hb
  have h2 (q : Pattern) (ha : d202016 q = 1) (hb : d251389 q = 1) : d251551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d251551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202016, d251551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d251389 q = 1) : d251553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d251553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62899 q ha hb
    | true =>
      simp only [d25289, d251553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d251389 q = 1) : d251554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d251554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d251554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202017 q = 1) (hb : d251389 q = 1) : d251555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d251555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d251555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202025 q = 1) (hb : d251389 q = 1) : d251565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d251565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202025, d251565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202026 q = 1) (hb : d251389 q = 1) : d251566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d251566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202026, d251566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d251389 q = 1) : d251567 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d251567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d251567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62902 (p : Pattern) (ha : d25319 p = 1) (hb : d251389 p = 1) : d251583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d251389 q = 1) : d251573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d251573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d251573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d251389 q = 1) : d251502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
    | true =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d251389 q = 1) : d251574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d251574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d251574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d251389 q = 1) : d251503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d251389 q = 1) : d251575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d251575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d251575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d251389 q = 1) : d251576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d251576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d251576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d251389 q = 1) : d251436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d251436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d251389 q = 1) : d251393 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62871 q ha hb
    | true =>
      simp only [d25105, d251393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d251389 q = 1) : d251437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d251437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d251389 q = 1) : d251394 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d251394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d251389 q = 1) : d251438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d251438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d251389 q = 1) : d251439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d251439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d251389 q = 1) : d251577 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d251577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d251577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25314 q = 1) (hb : d251389 q = 1) : d251578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
  have h15 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25315 q = 1) (hb : d251389 q = 1) : d251579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25316 q = 1) (hb : d251389 q = 1) : d251580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25317 q = 1) (hb : d251389 q = 1) : d251581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d251389 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d25318 q = 1) (hb : d251389 q = 1) : d251582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d251582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25318, d251582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d25319 q = 1) (hb : d251389 q = 1) : d251583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d251583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d251583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro62903 (p : Pattern) (ha : d25325 p = 1) (hb : d251389 p = 1) : d251589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d251389 q = 1) : d251584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62902 q ha hb
    | true =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d251389 q = 1) : d251585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d251389 q = 1) : d251586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25154 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
    | true =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25155 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25156 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25323 q = 1) (hb : d251389 q = 1) : d251587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d251389 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25157 q = 1) (hb : d251389 q = 1) : d251445 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25157, d251445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25324 q = 1) (hb : d251389 q = 1) : d251588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d251588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25324, d251588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25325 q = 1) (hb : d251389 q = 1) : d251589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d251589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25325, d251589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro62904 (p : Pattern) (ha : d25331 p = 1) (hb : d251389 p = 1) : d251595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d251389 q = 1) : d251590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d251590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62903 q ha hb
    | true =>
      simp only [d25326, d251590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d251389 q = 1) : d251591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d251591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d251591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d251389 q = 1) : d251448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62880 q ha hb
    | true =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d251389 q = 1) : d251449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d251389 q = 1) : d251592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d251592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d251592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d251389 q = 1) : d251593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d251593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d251593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d251389 q = 1) : d251594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d251594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d251594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d251389 q = 1) : d251595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d251595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d251595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62905 (p : Pattern) (ha : d25356 p = 1) (hb : d251389 p = 1) : d251601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d251389 q = 1) : d251448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62880 q ha hb
    | true =>
      simp only [d25160, d251448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d251389 q = 1) : d251449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d251449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d251389 q = 1) : d251598 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d251598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d251598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d251389 q = 1) : d251599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d251599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d251599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d251389 q = 1) : d251600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d251600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d251600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d251389 q = 1) : d251601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d251601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d251601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62906 (p : Pattern) (ha : d202037 p = 1) (hb : d251389 p = 1) : d251607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d251389 q = 1) : d251596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d251596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62904 q ha hb
    | true =>
      simp only [d25332, d251596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62881 q ha hb
  have h2 (q : Pattern) (ha : d202033 q = 1) (hb : d251389 q = 1) : d251597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d251597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202033, d251597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d251389 q = 1) : d251602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d251602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62905 q ha hb
    | true =>
      simp only [d25357, d251602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d251389 q = 1) : d251603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d251603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d251603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d251389 q = 1) : d251604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d251604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d251604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d251389 q = 1) : d251605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d251605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d251605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d251389 q = 1) : d251606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d251606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d251606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d251389 q = 1) : d251607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d251607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d251607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62907 (p : Pattern) (ha : d202043 p = 1) (hb : d251389 p = 1) : d251613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d251389 q = 1) : d251476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d251476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d251476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62884 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d251389 q = 1) : d251477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d251477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d251477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d251389 q = 1) : d251483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62884 q ha hb
    | true =>
      simp only [d25195, d251483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62885 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d251389 q = 1) : d251484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d251484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d251389 q = 1) : d251485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d251485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d251485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202021 q = 1) (hb : d251389 q = 1) : d251559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d251559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62895 q ha hb
    | true =>
      simp only [d202021, d251559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62900 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d251389 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25297 q = 1) (hb : d251389 q = 1) : d251561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d251561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62886 q ha hb
    | true =>
      simp only [d25297, d251561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202022 q = 1) (hb : d251389 q = 1) : d251562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d251562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d251562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202023 q = 1) (hb : d251389 q = 1) : d251563 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d251563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202023, d251563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d202024 q = 1) (hb : d251389 q = 1) : d251564 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d251564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202024, d251564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202028 q = 1) (hb : d251389 q = 1) : d251568 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d251568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202028, d251568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62901 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d251389 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d202029 q = 1) (hb : d251389 q = 1) : d251569 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d251569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202029, d251569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202030 q = 1) (hb : d251389 q = 1) : d251570 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d251570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202030, d251570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202031 q = 1) (hb : d251389 q = 1) : d251571 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d251571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202031, d251571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d202032 q = 1) (hb : d251389 q = 1) : d251572 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d251572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202032, d251572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202038 q = 1) (hb : d251389 q = 1) : d251608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d251608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202038, d251608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62906 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d251389 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d202039 q = 1) (hb : d251389 q = 1) : d251609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d251609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202039, d251609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202040 q = 1) (hb : d251389 q = 1) : d251610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d251610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202040, d251610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202041 q = 1) (hb : d251389 q = 1) : d251611 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d251611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202041, d251611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202042 q = 1) (hb : d251389 q = 1) : d251612 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d251612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202042, d251612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d202043 q = 1) (hb : d251389 q = 1) : d251613 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d251613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202043, d251613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro62908 (p : Pattern) (ha : d202049 p = 1) (hb : d251389 p = 1) : d251619 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d251389 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202006 q = 1) (hb : d251389 q = 1) : d251466 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d251466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202006, d251466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62883 q ha hb
  have h3 (q : Pattern) (ha : d202007 q = 1) (hb : d251389 q = 1) : d251467 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d251467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202007, d251467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202008 q = 1) (hb : d251389 q = 1) : d251468 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d251468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202008, d251468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202009 q = 1) (hb : d251389 q = 1) : d251469 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d251469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202009, d251469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202010 q = 1) (hb : d251389 q = 1) : d251470 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d251470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202010, d251470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202044 q = 1) (hb : d251389 q = 1) : d251614 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d251614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202044, d251614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62907 q ha hb
  have h8 (q : Pattern) (ha : d202045 q = 1) (hb : d251389 q = 1) : d251615 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d251615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202045, d251615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202046 q = 1) (hb : d251389 q = 1) : d251616 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d251616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202046, d251616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202047 q = 1) (hb : d251389 q = 1) : d251617 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d251617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202047, d251617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202048 q = 1) (hb : d251389 q = 1) : d251618 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d251618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202048, d251618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202049 q = 1) (hb : d251389 q = 1) : d251619 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d251619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202049, d251619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro62909 (p : Pattern) (ha : d25377 p = 1) (hb : d251389 p = 1) : d251622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d251389 q = 1) : d251516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62891 q ha hb
    | true =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d251389 q = 1) : d251517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d251389 q = 1) : d251518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25111 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
    | true =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25112 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25113 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25231 q = 1) (hb : d251389 q = 1) : d251519 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25375 q = 1) (hb : d251389 q = 1) : d251620 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d251620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25375, d251620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25376 q = 1) (hb : d251389 q = 1) : d251621 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d251621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25376, d251621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25377 q = 1) (hb : d251389 q = 1) : d251622 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d251622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25377, d251622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro62910 (p : Pattern) (ha : d25381 p = 1) (hb : d251389 p = 1) : d251626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25111 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
    | true =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25112 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25113 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25375 q = 1) (hb : d251389 q = 1) : d251620 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d251620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25375, d251620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25380 q = 1) (hb : d251389 q = 1) : d251625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d251625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25380, d251625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25381 q = 1) (hb : d251389 q = 1) : d251626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d251626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25381, d251626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62911 (p : Pattern) (ha : d25387 p = 1) (hb : d251389 p = 1) : d251632 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d251389 q = 1) : d251630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d251389 q = 1) : d251631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d251631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d251631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d251389 q = 1) : d251632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d251632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d251632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62912 (p : Pattern) (ha : d25391 p = 1) (hb : d251389 p = 1) : d251636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d251389 q = 1) : d251634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d251389 q = 1) : d251635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d251635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d251635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d251389 q = 1) : d251636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d251636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d251636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62913 (p : Pattern) (ha : d25397 p = 1) (hb : d251389 p = 1) : d251642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d251389 q = 1) : d251637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62911 q ha hb
    | true =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62912 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d251389 q = 1) : d251638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d251389 q = 1) : d251639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d251389 q = 1) : d251640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d251389 q = 1) : d251641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d251389 q = 1) : d251642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d251642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62914 (p : Pattern) (ha : d25400 p = 1) (hb : d251389 p = 1) : d251645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d251389 q = 1) : d251630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d251389 q = 1) : d251631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d251631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d251631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d251389 q = 1) : d251645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d251645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d251645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62915 (p : Pattern) (ha : d25401 p = 1) (hb : d251389 p = 1) : d251646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d251389 q = 1) : d251634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d251389 q = 1) : d251635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d251635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d251635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d251389 q = 1) : d251646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d251646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d251646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62916 (p : Pattern) (ha : d25407 p = 1) (hb : d251389 p = 1) : d251652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d251389 q = 1) : d251637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62911 q ha hb
    | true =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62912 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d251389 q = 1) : d251638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d251389 q = 1) : d251639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d251389 q = 1) : d251640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d251389 q = 1) : d251641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d251389 q = 1) : d251647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62914 q ha hb
    | true =>
      simp only [d25402, d251647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62915 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d251389 q = 1) : d251648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d251648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d251389 q = 1) : d251649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d251649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d251389 q = 1) : d251650 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d251650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d251389 q = 1) : d251651 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d251651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d251389 q = 1) : d251652 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d251652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62917 (p : Pattern) (ha : d25556 p = 1) (hb : d251389 p = 1) : d251752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d251389 q = 1) : d251637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62911 q ha hb
    | true =>
      simp only [d25392, d251637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62912 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d251389 q = 1) : d251638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d251638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d251389 q = 1) : d251639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d251639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d251389 q = 1) : d251640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d251640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d251389 q = 1) : d251641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d251641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d251389 q = 1) : d251747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d251747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62912 q ha hb
    | true =>
      simp only [d25551, d251747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d251389 q = 1) : d251748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d251748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d251748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d251389 q = 1) : d251749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d251749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d251749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d251389 q = 1) : d251750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d251750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d251750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d251389 q = 1) : d251751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d251751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d251751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d251389 q = 1) : d251752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d251752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d251752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62918 (p : Pattern) (ha : d25562 p = 1) (hb : d251389 p = 1) : d251758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d251389 q = 1) : d251747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d251747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62912 q ha hb
    | true =>
      simp only [d25551, d251747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d251389 q = 1) : d251748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d251748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d251748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d251389 q = 1) : d251749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d251749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d251749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d251389 q = 1) : d251750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d251750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d251750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d251389 q = 1) : d251751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d251751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d251751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d251389 q = 1) : d251753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d251753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62915 q ha hb
    | true =>
      simp only [d25557, d251753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d251389 q = 1) : d251754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d251754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d251754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d251389 q = 1) : d251755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d251755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d251755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d251389 q = 1) : d251756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d251756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d251756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d251389 q = 1) : d251757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d251757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d251757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d251389 q = 1) : d251758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d251758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d251758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62919 (p : Pattern) (ha : d25571 p = 1) (hb : d251389 p = 1) : d251767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d251389 q = 1) : d251753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d251753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62915 q ha hb
    | true =>
      simp only [d25557, d251753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d251389 q = 1) : d251754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d251754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d251754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d251389 q = 1) : d251755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d251755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d251755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d251389 q = 1) : d251756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d251756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d251756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d251389 q = 1) : d251757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d251757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d251757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d251389 q = 1) : d251767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d251767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d251767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62920 (p : Pattern) (ha : d25614 p = 1) (hb : d251389 p = 1) : d251810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25154 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
    | true =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25155 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25156 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25604 q = 1) (hb : d251389 q = 1) : d251800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d251800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25604, d251800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25613 q = 1) (hb : d251389 q = 1) : d251809 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d251809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25613, d251809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25614 q = 1) (hb : d251389 q = 1) : d251810 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d251810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25614, d251810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro62921 (p : Pattern) (ha : d25670 p = 1) (hb : d251389 p = 1) : d251833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d251389 q = 1) : d251811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d251811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62920 q ha hb
    | true =>
      simp only [d25615, d251811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d251389 q = 1) : d251812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d251812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d251812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d251389 q = 1) : d251830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d251830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d251830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d251389 q = 1) : d251831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d251831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d251831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d251389 q = 1) : d251832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d251832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d251832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d251389 q = 1) : d251833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d251833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d251833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62922 (p : Pattern) (ha : d25676 p = 1) (hb : d251389 p = 1) : d251839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d251389 q = 1) : d251834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d251834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62921 q ha hb
    | true =>
      simp only [d25671, d251834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d251389 q = 1) : d251835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d251835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d251835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d251389 q = 1) : d251836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d251836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d251836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d251389 q = 1) : d251837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d251837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d251837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d251389 q = 1) : d251838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d251838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d251838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d251389 q = 1) : d251839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d251839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d251839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62923 (p : Pattern) (ha : d25412 p = 1) (hb : d251389 p = 1) : d251657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d251389 q = 1) : d251630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d251389 q = 1) : d251656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d251656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d251656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d251389 q = 1) : d251657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d251657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d251657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62924 (p : Pattern) (ha : d25414 p = 1) (hb : d251389 p = 1) : d251659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d251389 q = 1) : d251634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d251389 q = 1) : d251658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d251658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d251658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d251389 q = 1) : d251659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d251659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d251659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62925 (p : Pattern) (ha : d25421 p = 1) (hb : d251389 p = 1) : d251666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d251389 q = 1) : d251664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d251664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d251664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d251389 q = 1) : d251665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d251665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d251665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d251389 q = 1) : d251666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d251666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d251666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62926 (p : Pattern) (ha : d25424 p = 1) (hb : d251389 p = 1) : d251669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d251389 q = 1) : d251667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d251667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d251667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d251389 q = 1) : d251668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d251668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d251668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d251389 q = 1) : d251669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d251669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d251669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62927 (p : Pattern) (ha : d25438 p = 1) (hb : d251389 p = 1) : d251677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25428 q = 1) (hb : d251389 q = 1) : d251673 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d537 q = 1) (hb : d202304 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48018 q ha hb
    | true =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d538 q = 1) (hb : d202304 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25429 q = 1) (hb : d251389 q = 1) : d251674 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, d251389, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25429, d251389, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25430 q = 1) (hb : d251389 q = 1) : d251675 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d251675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25430, d251675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25431 q = 1) (hb : d251389 q = 1) : d251676 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d251676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25431, d251676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d25435 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25436 q = 1) (hb : d251389 q = 1) : d251499 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25436, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25437 q = 1) (hb : d251389 q = 1) : d251500 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25437, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h17 (q : Pattern) (ha : d25438 q = 1) (hb : d251389 q = 1) : d251677 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d251677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25438, d251677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62928 (p : Pattern) (ha : d25443 p = 1) (hb : d251389 p = 1) : d251682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25211 q = 1) (hb : d251389 q = 1) : d251499 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25211, d251499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25212 q = 1) (hb : d251389 q = 1) : d251500 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25212, d251500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25219 q = 1) (hb : d251389 q = 1) : d251507 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h12 (q : Pattern) (ha : d25220 q = 1) (hb : d251389 q = 1) : d251508 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h13 (q : Pattern) (ha : d25443 q = 1) (hb : d251389 q = 1) : d251682 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d251682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25443, d251682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro62929 (p : Pattern) (ha : d25451 p = 1) (hb : d251389 p = 1) : d251690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25449 q = 1) (hb : d251389 q = 1) : d251688 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25450 q = 1) (hb : d251389 q = 1) : d251689 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d25219 q = 1) (hb : d251389 q = 1) : d251507 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25219, d251507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d25220 q = 1) (hb : d251389 q = 1) : d251508 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25220, d251508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d25451 q = 1) (hb : d251389 q = 1) : d251690 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, d251690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25451, d251690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro62930 (p : Pattern) (ha : d25457 p = 1) (hb : d251389 p = 1) : d251696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d251389 q = 1) : d251678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
    | true =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d251389 q = 1) : d251679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d251389 q = 1) : d251680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d251680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d251680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d251389 q = 1) : d251681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d251681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d251681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d251389 q = 1) : d251683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
    | true =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d251389 q = 1) : d251684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d251389 q = 1) : d251685 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d251685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d251685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d251389 q = 1) : d251686 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d251686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d251686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d251389 q = 1) : d251687 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d251687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d251687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d251389 q = 1) : d251693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d251389 q = 1) : d251694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25224 q = 1) (hb : d251389 q = 1) : d251512 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25225 q = 1) (hb : d251389 q = 1) : d251513 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25456 q = 1) (hb : d251389 q = 1) : d251695 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25456, d251695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25456, d251695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25457 q = 1) (hb : d251389 q = 1) : d251696 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d251696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d251696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62931 (p : Pattern) (ha : d25461 p = 1) (hb : d251389 p = 1) : d251700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25224 q = 1) (hb : d251389 q = 1) : d251512 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d251512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25225 q = 1) (hb : d251389 q = 1) : d251513 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25225, d251513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d251389 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25226 q = 1) (hb : d251389 q = 1) : d251514 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d251514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25226, d251514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d251389 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25461 q = 1) (hb : d251389 q = 1) : d251700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, d251700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25461, d251700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62932 (p : Pattern) (ha : d25467 p = 1) (hb : d251389 p = 1) : d251706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d251389 q = 1) : d251697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d251697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62930 q ha hb
    | true =>
      simp only [d25458, d251697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62891 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d251389 q = 1) : d251698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d251698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d251698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d251389 q = 1) : d251699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d251699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d251699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25462 q = 1) (hb : d251389 q = 1) : d251701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d251701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62891 q ha hb
    | true =>
      simp only [d25462, d251701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62931 q ha hb
  have h5 (q : Pattern) (ha : d25463 q = 1) (hb : d251389 q = 1) : d251702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d251702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d251702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25464 q = 1) (hb : d251389 q = 1) : d251703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d251703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d251703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25465 q = 1) (hb : d251389 q = 1) : d251704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d251704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d251704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25228 q = 1) (hb : d251389 q = 1) : d251516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62891 q ha hb
    | true =>
      simp only [d25228, d251516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
  have h9 (q : Pattern) (ha : d25229 q = 1) (hb : d251389 q = 1) : d251517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d251517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25230 q = 1) (hb : d251389 q = 1) : d251518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d251518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d251389 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25111 q = 1) (hb : d251389 q = 1) : d251399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62872 q ha hb
    | true =>
      simp only [d25111, d251399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25112 q = 1) (hb : d251389 q = 1) : d251400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d251400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25113 q = 1) (hb : d251389 q = 1) : d251401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d251401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25231 q = 1) (hb : d251389 q = 1) : d251519 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25231, d251519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25466 q = 1) (hb : d251389 q = 1) : d251705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d251705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25466, d251705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25467 q = 1) (hb : d251389 q = 1) : d251706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d251706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25467, d251706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro62933 (p : Pattern) (ha : d25473 p = 1) (hb : d251389 p = 1) : d251712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d251389 q = 1) : d251707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d251707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62932 q ha hb
    | true =>
      simp only [d25468, d251707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d251389 q = 1) : d251708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d251708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d251708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d251389 q = 1) : d251709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d251709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d251709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d251389 q = 1) : d251710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d251710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d251710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d251389 q = 1) : d251711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d251711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d251711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d251389 q = 1) : d251712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d251712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d251712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62934 (p : Pattern) (ha : d25519 p = 1) (hb : d251389 p = 1) : d251718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d251389 q = 1) : d251715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d251715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d251715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d251389 q = 1) : d251716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d251716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d251716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d251389 q = 1) : d251717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d251717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d251717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d251389 q = 1) : d251718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d251718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d251718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62935 (p : Pattern) (ha : d202054 p = 1) (hb : d251389 p = 1) : d251724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d251389 q = 1) : d251660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d251660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62923 q ha hb
    | true =>
      simp only [d25415, d251660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62924 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d251389 q = 1) : d251661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d251661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d251661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d251389 q = 1) : d251662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d251662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d251662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d251389 q = 1) : d251663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d251663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d251663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d251389 q = 1) : d251670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d251670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62925 q ha hb
    | true =>
      simp only [d25425, d251670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62926 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d251389 q = 1) : d251671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d251671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d251671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d251389 q = 1) : d251672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d251672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d251672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d251389 q = 1) : d251713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d251713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62933 q ha hb
    | true =>
      simp only [d25474, d251713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62911 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d251389 q = 1) : d251714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d251714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d251714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d251389 q = 1) : d251719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d251719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62934 q ha hb
    | true =>
      simp only [d25520, d251719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d251389 q = 1) : d251720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d251720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d251720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d251389 q = 1) : d251721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d251721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d251721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d251389 q = 1) : d251722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d251722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d251722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d251389 q = 1) : d251723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d251723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d251723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202054 q = 1) (hb : d251389 q = 1) : d251724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d251724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d251724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62936 (p : Pattern) (ha : d25526 p = 1) (hb : d251389 p = 1) : d251725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d251389 q = 1) : d251630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d251630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d251389 q = 1) : d251656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d251656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d251656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d251389 q = 1) : d251725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d251725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d251725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62937 (p : Pattern) (ha : d25527 p = 1) (hb : d251389 p = 1) : d251726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d251389 q = 1) : d251634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d251634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d251389 q = 1) : d251658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d251658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d251658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d251389 q = 1) : d251726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d251726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d251726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62938 (p : Pattern) (ha : d25532 p = 1) (hb : d251389 p = 1) : d251731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d251389 q = 1) : d251629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d251629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d251389 q = 1) : d251664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d251664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d251664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d251389 q = 1) : d251665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d251665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d251665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d251389 q = 1) : d251731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d251731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d251731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62939 (p : Pattern) (ha : d25533 p = 1) (hb : d251389 p = 1) : d251732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d251389 q = 1) : d251627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62910 q ha hb
    | true =>
      simp only [d25382, d251627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d251389 q = 1) : d251628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d251628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d251389 q = 1) : d251633 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d251633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d251389 q = 1) : d251667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d251667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d251667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d251389 q = 1) : d251668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d251668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d251668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d251389 q = 1) : d251732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d251732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d251732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62940 (p : Pattern) (ha : d25537 p = 1) (hb : d251389 p = 1) : d251736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d251389 q = 1) : d251707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d251707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62932 q ha hb
    | true =>
      simp only [d25468, d251707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d251389 q = 1) : d251708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d251708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d251708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d251389 q = 1) : d251709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d251709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d251709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d251389 q = 1) : d251710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d251710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d251710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d251389 q = 1) : d251711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d251711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d251711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d251389 q = 1) : d251736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d251736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d251736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62941 (p : Pattern) (ha : d25543 p = 1) (hb : d251389 p = 1) : d251739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d251389 q = 1) : d251623 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62909 q ha hb
    | true =>
      simp only [d25378, d251623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d251389 q = 1) : d251624 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d251624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d251389 q = 1) : d251715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d251715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d251715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d251389 q = 1) : d251716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d251716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d251716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d251389 q = 1) : d251717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d251717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d251717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d251389 q = 1) : d251739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d251739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d251739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62942 (p : Pattern) (ha : d202059 p = 1) (hb : d251389 p = 1) : d251745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d251389 q = 1) : d251660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d251660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62923 q ha hb
    | true =>
      simp only [d25415, d251660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62924 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d251389 q = 1) : d251661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d251661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d251661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d251389 q = 1) : d251662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d251662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d251662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d251389 q = 1) : d251663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d251663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d251663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d251389 q = 1) : d251670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d251670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62925 q ha hb
    | true =>
      simp only [d25425, d251670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62926 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d251389 q = 1) : d251671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d251671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d251671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d251389 q = 1) : d251672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d251672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d251672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d251389 q = 1) : d251713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d251713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62933 q ha hb
    | true =>
      simp only [d25474, d251713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62911 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d251389 q = 1) : d251714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d251714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d251714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d251389 q = 1) : d251719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d251719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62934 q ha hb
    | true =>
      simp only [d25520, d251719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d251389 q = 1) : d251720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d251720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d251720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d251389 q = 1) : d251721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d251721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d251721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d251389 q = 1) : d251722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d251722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d251722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d251389 q = 1) : d251723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d251723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d251723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d251389 q = 1) : d251727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d251727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62936 q ha hb
    | true =>
      simp only [d25528, d251727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62937 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d251389 q = 1) : d251728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d251728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d251728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d251389 q = 1) : d251729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d251729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d251729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d251389 q = 1) : d251730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d251730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d251730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d251389 q = 1) : d251733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d251733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62938 q ha hb
    | true =>
      simp only [d25534, d251733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62939 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d251389 q = 1) : d251734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d251734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d251734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d251389 q = 1) : d251735 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d251735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d251735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d251389 q = 1) : d251737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d251737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62940 q ha hb
    | true =>
      simp only [d25538, d251737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62914 q ha hb
  have h23 (q : Pattern) (ha : d202055 q = 1) (hb : d251389 q = 1) : d251738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d251738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202055, d251738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d251389 q = 1) : d251740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d251740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62941 q ha hb
    | true =>
      simp only [d25544, d251740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d251389 q = 1) : d251741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d251741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d251741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202056 q = 1) (hb : d251389 q = 1) : d251742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d251742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d251742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202057 q = 1) (hb : d251389 q = 1) : d251743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d251743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202057, d251743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202058 q = 1) (hb : d251389 q = 1) : d251744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d251744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202058, d251744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202059 q = 1) (hb : d251389 q = 1) : d251745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d251745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d251745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62943 (p : Pattern) (ha : d202066 p = 1) (hb : d251389 p = 1) : d251765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d251389 q = 1) : d251737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d251737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62940 q ha hb
    | true =>
      simp only [d25538, d251737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62914 q ha hb
  have h2 (q : Pattern) (ha : d202055 q = 1) (hb : d251389 q = 1) : d251738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d251738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202055, d251738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d251389 q = 1) : d251740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d251740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62941 q ha hb
    | true =>
      simp only [d25544, d251740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d251389 q = 1) : d251741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d251741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d251741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d251389 q = 1) : d251742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d251742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d251742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d251389 q = 1) : d251763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d251763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d251763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d251389 q = 1) : d251764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d251764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d251764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d251389 q = 1) : d251765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d251765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d251765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62944 (p : Pattern) (ha : d25591 p = 1) (hb : d251389 p = 1) : d251787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d251389 q = 1) : d251773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d251773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d251773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d251389 q = 1) : d251678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
    | true =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d251389 q = 1) : d251774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d251774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d251774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d251389 q = 1) : d251679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d251389 q = 1) : d251775 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d251775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d251775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d251389 q = 1) : d251776 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d251776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d251776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d251389 q = 1) : d251777 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d251777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d251777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d251389 q = 1) : d251683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
    | true =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d251389 q = 1) : d251778 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d251778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d251778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d251389 q = 1) : d251684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d251389 q = 1) : d251779 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d251779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d251779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d251389 q = 1) : d251780 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d251780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d251780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d251389 q = 1) : d251781 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d251781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d251781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25586 q = 1) (hb : d251389 q = 1) : d251782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
  have h15 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25587 q = 1) (hb : d251389 q = 1) : d251783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25588 q = 1) (hb : d251389 q = 1) : d251784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25589 q = 1) (hb : d251389 q = 1) : d251785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25314 q = 1) (hb : d251389 q = 1) : d251578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
  have h21 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25315 q = 1) (hb : d251389 q = 1) : d251579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25316 q = 1) (hb : d251389 q = 1) : d251580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25317 q = 1) (hb : d251389 q = 1) : d251581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25590 q = 1) (hb : d251389 q = 1) : d251786 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25590, d251786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25590, d251786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25591 q = 1) (hb : d251389 q = 1) : d251787 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d251787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d251787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro62945 (p : Pattern) (ha : d25595 p = 1) (hb : d251389 p = 1) : d251791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25314 q = 1) (hb : d251389 q = 1) : d251578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d251578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
  have h2 (q : Pattern) (ha : d25222 q = 1) (hb : d251389 q = 1) : d251510 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62890 q ha hb
    | true =>
      simp only [d25222, d251510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25315 q = 1) (hb : d251389 q = 1) : d251579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25315, d251579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25223 q = 1) (hb : d251389 q = 1) : d251511 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25223, d251511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25316 q = 1) (hb : d251389 q = 1) : d251580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25316, d251580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25317 q = 1) (hb : d251389 q = 1) : d251581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25317, d251581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d251389 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25318 q = 1) (hb : d251389 q = 1) : d251582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d251582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25318, d251582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d251389 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25595 q = 1) (hb : d251389 q = 1) : d251791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25595, d251791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25595, d251791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62946 (p : Pattern) (ha : d25601 p = 1) (hb : d251389 p = 1) : d251797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25592 q = 1) (hb : d251389 q = 1) : d251788 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25592, d251788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62944 q ha hb
    | true =>
      simp only [d25592, d251788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62902 q ha hb
  have h2 (q : Pattern) (ha : d25593 q = 1) (hb : d251389 q = 1) : d251789 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25593, d251789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25593, d251789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25594 q = 1) (hb : d251389 q = 1) : d251790 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25594, d251790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25594, d251790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25596 q = 1) (hb : d251389 q = 1) : d251792 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25596, d251792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62902 q ha hb
    | true =>
      simp only [d25596, d251792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62945 q ha hb
  have h5 (q : Pattern) (ha : d25597 q = 1) (hb : d251389 q = 1) : d251793 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25597, d251793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25597, d251793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25598 q = 1) (hb : d251389 q = 1) : d251794 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25598, d251794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25598, d251794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25599 q = 1) (hb : d251389 q = 1) : d251795 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25599, d251795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25599, d251795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25320 q = 1) (hb : d251389 q = 1) : d251584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62902 q ha hb
    | true =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
  have h9 (q : Pattern) (ha : d25321 q = 1) (hb : d251389 q = 1) : d251585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25322 q = 1) (hb : d251389 q = 1) : d251586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25154 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
    | true =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25155 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25156 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25323 q = 1) (hb : d251389 q = 1) : d251587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25600 q = 1) (hb : d251389 q = 1) : d251796 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25600, d251796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25600, d251796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25601 q = 1) (hb : d251389 q = 1) : d251797 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25601, d251797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25601, d251797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro62947 (p : Pattern) (ha : d25606 p = 1) (hb : d251389 p = 1) : d251802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d251389 q = 1) : d251584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62902 q ha hb
    | true =>
      simp only [d25320, d251584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d251389 q = 1) : d251585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d251585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d251389 q = 1) : d251586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d251586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d251389 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25154 q = 1) (hb : d251389 q = 1) : d251442 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62879 q ha hb
    | true =>
      simp only [d25154, d251442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25155 q = 1) (hb : d251389 q = 1) : d251443 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d251443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25156 q = 1) (hb : d251389 q = 1) : d251444 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d251444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25323 q = 1) (hb : d251389 q = 1) : d251587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d251587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25604 q = 1) (hb : d251389 q = 1) : d251800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d251800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25604, d251800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25605 q = 1) (hb : d251389 q = 1) : d251801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25605, d251801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25605, d251801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25606 q = 1) (hb : d251389 q = 1) : d251802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25606, d251802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25606, d251802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro62948 (p : Pattern) (ha : d25612 p = 1) (hb : d251389 p = 1) : d251808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25602 q = 1) (hb : d251389 q = 1) : d251798 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25602, d251798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62946 q ha hb
    | true =>
      simp only [d25602, d251798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25603 q = 1) (hb : d251389 q = 1) : d251799 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25603, d251799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25603, d251799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25607 q = 1) (hb : d251389 q = 1) : d251803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62947 q ha hb
    | true =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25608 q = 1) (hb : d251389 q = 1) : d251804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25609 q = 1) (hb : d251389 q = 1) : d251805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25609, d251805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25609, d251805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25610 q = 1) (hb : d251389 q = 1) : d251806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25610, d251806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25610, d251806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25611 q = 1) (hb : d251389 q = 1) : d251807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25611, d251807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25611, d251807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25612 q = 1) (hb : d251389 q = 1) : d251808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25612, d251808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25612, d251808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62949 (p : Pattern) (ha : d25620 p = 1) (hb : d251389 p = 1) : d251816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d251389 q = 1) : d251803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62947 q ha hb
    | true =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d251389 q = 1) : d251804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25615 q = 1) (hb : d251389 q = 1) : d251811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d251811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62920 q ha hb
    | true =>
      simp only [d25615, d251811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25616 q = 1) (hb : d251389 q = 1) : d251812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d251812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d251812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25617 q = 1) (hb : d251389 q = 1) : d251813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25617, d251813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25617, d251813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25618 q = 1) (hb : d251389 q = 1) : d251814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25618, d251814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25618, d251814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25619 q = 1) (hb : d251389 q = 1) : d251815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25619, d251815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25619, d251815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25620 q = 1) (hb : d251389 q = 1) : d251816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25620, d251816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25620, d251816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62950 (p : Pattern) (ha : d25659 p = 1) (hb : d251389 p = 1) : d251822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d251389 q = 1) : d251803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62947 q ha hb
    | true =>
      simp only [d25607, d251803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d251389 q = 1) : d251804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d251804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25656 q = 1) (hb : d251389 q = 1) : d251819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25656, d251819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25656, d251819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25657 q = 1) (hb : d251389 q = 1) : d251820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25657, d251820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25657, d251820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25658 q = 1) (hb : d251389 q = 1) : d251821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25658, d251821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25658, d251821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25659 q = 1) (hb : d251389 q = 1) : d251822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25659, d251822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25659, d251822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62951 (p : Pattern) (ha : d202076 p = 1) (hb : d251389 p = 1) : d251828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25621 q = 1) (hb : d251389 q = 1) : d251817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25621, d251817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62948 q ha hb
    | true =>
      simp only [d25621, d251817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62949 q ha hb
  have h2 (q : Pattern) (ha : d202072 q = 1) (hb : d251389 q = 1) : d251818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d251818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202072, d251818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25660 q = 1) (hb : d251389 q = 1) : d251823 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25660, d251823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62950 q ha hb
    | true =>
      simp only [d25660, d251823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25661 q = 1) (hb : d251389 q = 1) : d251824 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25661, d251824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25661, d251824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202073 q = 1) (hb : d251389 q = 1) : d251825 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d251825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202073, d251825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202074 q = 1) (hb : d251389 q = 1) : d251826 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d251826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202074, d251826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202075 q = 1) (hb : d251389 q = 1) : d251827 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d251827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202075, d251827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202076 q = 1) (hb : d251389 q = 1) : d251828 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d251828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202076, d251828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62952 (p : Pattern) (ha : d202082 p = 1) (hb : d251389 p = 1) : d251845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25398 q = 1) (hb : d251389 q = 1) : d251643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25398, d251643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25398, d251643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62913 q ha hb
  have h2 (q : Pattern) (ha : d25399 q = 1) (hb : d251389 q = 1) : d251644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25399, d251644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25399, d251644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25408 q = 1) (hb : d251389 q = 1) : d251653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62913 q ha hb
    | true =>
      simp only [d25408, d251653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62916 q ha hb
  have h4 (q : Pattern) (ha : d25409 q = 1) (hb : d251389 q = 1) : d251654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25409, d251654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25410 q = 1) (hb : d251389 q = 1) : d251655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25410, d251655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25410, d251655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202060 q = 1) (hb : d251389 q = 1) : d251746 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d251746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62935 q ha hb
    | true =>
      simp only [d202060, d251746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62942 q ha hb
  have h7 (q : Pattern) (ha : d25563 q = 1) (hb : d251389 q = 1) : d251759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25563, d251759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62917 q ha hb
    | true =>
      simp only [d25563, d251759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62918 q ha hb
  have h8 (q : Pattern) (ha : d202061 q = 1) (hb : d251389 q = 1) : d251760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d251760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202061, d251760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202062 q = 1) (hb : d251389 q = 1) : d251761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d251761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202062, d251761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202063 q = 1) (hb : d251389 q = 1) : d251762 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d251762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202063, d251762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202067 q = 1) (hb : d251389 q = 1) : d251766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d251766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202067, d251766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62943 q ha hb
  have h12 (q : Pattern) (ha : d25572 q = 1) (hb : d251389 q = 1) : d251768 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25572, d251768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25572, d251768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62919 q ha hb
  have h13 (q : Pattern) (ha : d202068 q = 1) (hb : d251389 q = 1) : d251769 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d251769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202068, d251769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202069 q = 1) (hb : d251389 q = 1) : d251770 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d251770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202069, d251770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202070 q = 1) (hb : d251389 q = 1) : d251771 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d251771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202070, d251771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202071 q = 1) (hb : d251389 q = 1) : d251772 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d251772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202071, d251772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202077 q = 1) (hb : d251389 q = 1) : d251829 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d251829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202077, d251829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62951 q ha hb
  have h18 (q : Pattern) (ha : d25677 q = 1) (hb : d251389 q = 1) : d251840 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25677, d251840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25677, d251840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62922 q ha hb
  have h19 (q : Pattern) (ha : d202078 q = 1) (hb : d251389 q = 1) : d251841 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d251841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202078, d251841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202079 q = 1) (hb : d251389 q = 1) : d251842 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d251842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202079, d251842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202080 q = 1) (hb : d251389 q = 1) : d251843 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d251843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202080, d251843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202081 q = 1) (hb : d251389 q = 1) : d251844 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d251844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202081, d251844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202082 q = 1) (hb : d251389 q = 1) : d251845 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d251845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202082, d251845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62953 (p : Pattern) (ha : d202088 p = 1) (hb : d251389 p = 1) : d251851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202083 q = 1) (hb : d251389 q = 1) : d251846 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d251846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202083, d251846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62952 q ha hb
  have h2 (q : Pattern) (ha : d202084 q = 1) (hb : d251389 q = 1) : d251847 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d251847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202084, d251847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202085 q = 1) (hb : d251389 q = 1) : d251848 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d251848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202085, d251848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202086 q = 1) (hb : d251389 q = 1) : d251849 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d251849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202086, d251849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202087 q = 1) (hb : d251389 q = 1) : d251850 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d251850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202087, d251850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202088 q = 1) (hb : d251389 q = 1) : d251851 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d251851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202088, d251851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62954 (p : Pattern) (ha : d25690 p = 1) (hb : d251389 p = 1) : d251853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d202304 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47928 q ha hb
    | true =>
      simp only [d133, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d202304 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9796 q = 1) (hb : d251389 q = 1) : d25435 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9796, d251389, d25435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d251389 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25102 q = 1) (hb : d251389 q = 1) : d251390 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25102, d251390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25103 q = 1) (hb : d251389 q = 1) : d251391 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25103, d251391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25690 q = 1) (hb : d251389 q = 1) : d251853 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25690, d251853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25690, d251853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro62955 (p : Pattern) (ha : d25696 p = 1) (hb : d251389 p = 1) : d251859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d251389 q = 1) : d251678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
    | true =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d251389 q = 1) : d251679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d251389 q = 1) : d251680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d251680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d251680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d251389 q = 1) : d251681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d251681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d251681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d251389 q = 1) : d251683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
    | true =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d251389 q = 1) : d251684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d251389 q = 1) : d251685 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d251685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d251685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d251389 q = 1) : d251686 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d251686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d251686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d251389 q = 1) : d251687 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d251687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d251687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25454 q = 1) (hb : d251389 q = 1) : d251693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25455 q = 1) (hb : d251389 q = 1) : d251694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25693 q = 1) (hb : d251389 q = 1) : d251856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25694 q = 1) (hb : d251389 q = 1) : d251857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25695 q = 1) (hb : d251389 q = 1) : d251858 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d251858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25695, d251858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25696 q = 1) (hb : d251389 q = 1) : d251859 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25696, d251859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25696, d251859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62956 (p : Pattern) (ha : d25699 p = 1) (hb : d251389 p = 1) : d251862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d251389 q = 1) : d251502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
    | true =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d251389 q = 1) : d251503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d251389 q = 1) : d251504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d251504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d251504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d251389 q = 1) : d251505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d251505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d251505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25693 q = 1) (hb : d251389 q = 1) : d251856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25694 q = 1) (hb : d251389 q = 1) : d251857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25697 q = 1) (hb : d251389 q = 1) : d251860 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25697, d251860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25697, d251860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25698 q = 1) (hb : d251389 q = 1) : d251861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25699 q = 1) (hb : d251389 q = 1) : d251862 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25699, d251862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25699, d251862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62957 (p : Pattern) (ha : d25703 p = 1) (hb : d251389 p = 1) : d251866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25693 q = 1) (hb : d251389 q = 1) : d251856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25694 q = 1) (hb : d251389 q = 1) : d251857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25698 q = 1) (hb : d251389 q = 1) : d251861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25703 q = 1) (hb : d251389 q = 1) : d251866 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25703, d251866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25703, d251866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62958 (p : Pattern) (ha : d25710 p = 1) (hb : d251389 p = 1) : d251873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25700 q = 1) (hb : d251389 q = 1) : d251863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d251863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62955 q ha hb
    | true =>
      simp only [d25700, d251863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62956 q ha hb
  have h2 (q : Pattern) (ha : d25701 q = 1) (hb : d251389 q = 1) : d251864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d251864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d251864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25702 q = 1) (hb : d251389 q = 1) : d251865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d251865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d251865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25704 q = 1) (hb : d251389 q = 1) : d251867 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62956 q ha hb
    | true =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62957 q ha hb
  have h5 (q : Pattern) (ha : d25705 q = 1) (hb : d251389 q = 1) : d251868 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25706 q = 1) (hb : d251389 q = 1) : d251869 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25707 q = 1) (hb : d251389 q = 1) : d251870 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d251870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25707, d251870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25708 q = 1) (hb : d251389 q = 1) : d251871 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d251871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25708, d251871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25709 q = 1) (hb : d251389 q = 1) : d251872 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25709, d251872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25709, d251872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25710 q = 1) (hb : d251389 q = 1) : d251873 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25710, d251873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25710, d251873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62959 (p : Pattern) (ha : d25714 p = 1) (hb : d251389 p = 1) : d251877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25704 q = 1) (hb : d251389 q = 1) : d251867 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62956 q ha hb
    | true =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62957 q ha hb
  have h2 (q : Pattern) (ha : d25705 q = 1) (hb : d251389 q = 1) : d251868 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25706 q = 1) (hb : d251389 q = 1) : d251869 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25708 q = 1) (hb : d251389 q = 1) : d251871 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d251871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25708, d251871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25713 q = 1) (hb : d251389 q = 1) : d251876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25713, d251876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25713, d251876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25714 q = 1) (hb : d251389 q = 1) : d251877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25714, d251877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25714, d251877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62960 (p : Pattern) (ha : d25720 p = 1) (hb : d251389 p = 1) : d251883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d251389 q = 1) : d251881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d251389 q = 1) : d251882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d251882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d251882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25720 q = 1) (hb : d251389 q = 1) : d251883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25720, d251883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25720, d251883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62961 (p : Pattern) (ha : d25724 p = 1) (hb : d251389 p = 1) : d251887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d251389 q = 1) : d251885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d251389 q = 1) : d251886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d251886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d251886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25724 q = 1) (hb : d251389 q = 1) : d251887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25724, d251887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25724, d251887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62962 (p : Pattern) (ha : d25730 p = 1) (hb : d251389 p = 1) : d251893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d251389 q = 1) : d251888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62960 q ha hb
    | true =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62961 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d251389 q = 1) : d251889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d251389 q = 1) : d251890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d251389 q = 1) : d251891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d251389 q = 1) : d251892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25730 q = 1) (hb : d251389 q = 1) : d251893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25730, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25730, d251893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62963 (p : Pattern) (ha : d25733 p = 1) (hb : d251389 p = 1) : d251896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d251389 q = 1) : d251881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d251389 q = 1) : d251882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d251882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d251882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25733 q = 1) (hb : d251389 q = 1) : d251896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25733, d251896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25733, d251896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62964 (p : Pattern) (ha : d25734 p = 1) (hb : d251389 p = 1) : d251897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d251389 q = 1) : d251885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d251389 q = 1) : d251886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d251886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d251886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25734 q = 1) (hb : d251389 q = 1) : d251897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25734, d251897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25734, d251897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62965 (p : Pattern) (ha : d25740 p = 1) (hb : d251389 p = 1) : d251903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d251389 q = 1) : d251888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62960 q ha hb
    | true =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62961 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d251389 q = 1) : d251889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d251389 q = 1) : d251890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d251389 q = 1) : d251891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d251389 q = 1) : d251892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25735 q = 1) (hb : d251389 q = 1) : d251898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62963 q ha hb
    | true =>
      simp only [d25735, d251898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62964 q ha hb
  have h7 (q : Pattern) (ha : d25736 q = 1) (hb : d251389 q = 1) : d251899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d251899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25737 q = 1) (hb : d251389 q = 1) : d251900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25737, d251900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25738 q = 1) (hb : d251389 q = 1) : d251901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d251901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25739 q = 1) (hb : d251389 q = 1) : d251902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d251902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25740 q = 1) (hb : d251389 q = 1) : d251903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25740, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25740, d251903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62966 (p : Pattern) (ha : d25912 p = 1) (hb : d251389 p = 1) : d252005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d251389 q = 1) : d251888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62960 q ha hb
    | true =>
      simp only [d25725, d251888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62961 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d251389 q = 1) : d251889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d251889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d251389 q = 1) : d251890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d251890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d251389 q = 1) : d251891 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d251891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d251389 q = 1) : d251892 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d251892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25907 q = 1) (hb : d251389 q = 1) : d252000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d252000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62961 q ha hb
    | true =>
      simp only [d25907, d252000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25908 q = 1) (hb : d251389 q = 1) : d252001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d252001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d252001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25909 q = 1) (hb : d251389 q = 1) : d252002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d252002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25909, d252002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25910 q = 1) (hb : d251389 q = 1) : d252003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d252003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d252003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25911 q = 1) (hb : d251389 q = 1) : d252004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d252004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d252004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25912 q = 1) (hb : d251389 q = 1) : d252005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25912, d252005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25912, d252005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62967 (p : Pattern) (ha : d25918 p = 1) (hb : d251389 p = 1) : d252011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25907 q = 1) (hb : d251389 q = 1) : d252000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d252000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62961 q ha hb
    | true =>
      simp only [d25907, d252000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25908 q = 1) (hb : d251389 q = 1) : d252001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d252001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d252001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25909 q = 1) (hb : d251389 q = 1) : d252002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d252002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25909, d252002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25910 q = 1) (hb : d251389 q = 1) : d252003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d252003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d252003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25911 q = 1) (hb : d251389 q = 1) : d252004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d252004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d252004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25913 q = 1) (hb : d251389 q = 1) : d252006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d252006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62964 q ha hb
    | true =>
      simp only [d25913, d252006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25914 q = 1) (hb : d251389 q = 1) : d252007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d252007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d252007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25915 q = 1) (hb : d251389 q = 1) : d252008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d252008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25915, d252008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25916 q = 1) (hb : d251389 q = 1) : d252009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d252009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d252009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25917 q = 1) (hb : d251389 q = 1) : d252010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d252010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d252010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25918 q = 1) (hb : d251389 q = 1) : d252011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25918, d252011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25918, d252011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62968 (p : Pattern) (ha : d25927 p = 1) (hb : d251389 p = 1) : d252020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25913 q = 1) (hb : d251389 q = 1) : d252006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d252006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62964 q ha hb
    | true =>
      simp only [d25913, d252006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25914 q = 1) (hb : d251389 q = 1) : d252007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d252007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d252007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25915 q = 1) (hb : d251389 q = 1) : d252008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d252008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25915, d252008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25916 q = 1) (hb : d251389 q = 1) : d252009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d252009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d252009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25917 q = 1) (hb : d251389 q = 1) : d252010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d252010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d252010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25927 q = 1) (hb : d251389 q = 1) : d252020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25927, d252020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25927, d252020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62969 (p : Pattern) (ha : d25964 p = 1) (hb : d251389 p = 1) : d252057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d251389 q = 1) : d251573 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d251573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d251573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d251389 q = 1) : d251502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62889 q ha hb
    | true =>
      simp only [d25214, d251502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d251389 q = 1) : d251574 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d251574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d251574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d251389 q = 1) : d251503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d251503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d251389 q = 1) : d251575 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d251575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d251575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d251389 q = 1) : d251576 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d251576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d251576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25948 q = 1) (hb : d251389 q = 1) : d252041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
  have h8 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25949 q = 1) (hb : d251389 q = 1) : d252042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25950 q = 1) (hb : d251389 q = 1) : d252043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25951 q = 1) (hb : d251389 q = 1) : d252044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25963 q = 1) (hb : d251389 q = 1) : d252056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25963, d252056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25963, d252056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25957 q = 1) (hb : d251389 q = 1) : d252050 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25964 q = 1) (hb : d251389 q = 1) : d252057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25964, d252057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25964, d252057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62970 (p : Pattern) (ha : d25968 p = 1) (hb : d251389 p = 1) : d252061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25948 q = 1) (hb : d251389 q = 1) : d252041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
  have h2 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25949 q = 1) (hb : d251389 q = 1) : d252042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25950 q = 1) (hb : d251389 q = 1) : d252043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25951 q = 1) (hb : d251389 q = 1) : d252044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25957 q = 1) (hb : d251389 q = 1) : d252050 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25968 q = 1) (hb : d251389 q = 1) : d252061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25968, d252061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25968, d252061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62971 (p : Pattern) (ha : d25987 p = 1) (hb : d251389 p = 1) : d252080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25969 q = 1) (hb : d251389 q = 1) : d252062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62969 q ha hb
    | true =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62970 q ha hb
  have h2 (q : Pattern) (ha : d25970 q = 1) (hb : d251389 q = 1) : d252063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25971 q = 1) (hb : d251389 q = 1) : d252064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25977 q = 1) (hb : d251389 q = 1) : d252070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d252070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25977, d252070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25986 q = 1) (hb : d251389 q = 1) : d252079 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25986, d252079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25986, d252079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25987 q = 1) (hb : d251389 q = 1) : d252080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25987, d252080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25987, d252080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62972 (p : Pattern) (ha : d26058 p = 1) (hb : d251389 p = 1) : d252103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25988 q = 1) (hb : d251389 q = 1) : d252081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d252081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62971 q ha hb
    | true =>
      simp only [d25988, d252081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25989 q = 1) (hb : d251389 q = 1) : d252082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d252082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d252082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26055 q = 1) (hb : d251389 q = 1) : d252100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26055, d252100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26055, d252100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26056 q = 1) (hb : d251389 q = 1) : d252101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26056, d252101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26056, d252101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26057 q = 1) (hb : d251389 q = 1) : d252102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26057, d252102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26057, d252102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26058 q = 1) (hb : d251389 q = 1) : d252103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26058, d252103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26058, d252103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62973 (p : Pattern) (ha : d26064 p = 1) (hb : d251389 p = 1) : d252109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26059 q = 1) (hb : d251389 q = 1) : d252104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26059, d252104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62972 q ha hb
    | true =>
      simp only [d26059, d252104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26060 q = 1) (hb : d251389 q = 1) : d252105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26060, d252105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26060, d252105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26061 q = 1) (hb : d251389 q = 1) : d252106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26061, d252106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26061, d252106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26062 q = 1) (hb : d251389 q = 1) : d252107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26062, d252107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26062, d252107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26063 q = 1) (hb : d251389 q = 1) : d252108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26063, d252108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26063, d252108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26064 q = 1) (hb : d251389 q = 1) : d252109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26064, d252109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26064, d252109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62974 (p : Pattern) (ha : d25745 p = 1) (hb : d251389 p = 1) : d251908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d251389 q = 1) : d251881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d251389 q = 1) : d251907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d251907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d251907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25745 q = 1) (hb : d251389 q = 1) : d251908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25745, d251908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25745, d251908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62975 (p : Pattern) (ha : d25747 p = 1) (hb : d251389 p = 1) : d251910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d251389 q = 1) : d251885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d251389 q = 1) : d251909 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d251909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d251909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25747 q = 1) (hb : d251389 q = 1) : d251910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25747, d251910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25747, d251910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62976 (p : Pattern) (ha : d25754 p = 1) (hb : d251389 p = 1) : d251917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d251389 q = 1) : d251915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d251915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d251915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d251389 q = 1) : d251916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d251916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d251916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25754 q = 1) (hb : d251389 q = 1) : d251917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25754, d251917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25754, d251917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62977 (p : Pattern) (ha : d25757 p = 1) (hb : d251389 p = 1) : d251920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d251389 q = 1) : d251918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d251918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d251918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d251389 q = 1) : d251919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d251919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d251919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25757 q = 1) (hb : d251389 q = 1) : d251920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25757, d251920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25757, d251920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62978 (p : Pattern) (ha : d25770 p = 1) (hb : d251389 p = 1) : d251930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d202304 q = 1) : d31303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48082 q ha hb
    | true =>
      simp only [d822, d31303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d31304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9759 q = 1) (hb : d251389 q = 1) : d251924 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d251389, d251924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9759, d251389, d251924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d828 q = 1) (hb : d202304 q = 1) : d28880 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48083 q ha hb
    | true =>
      simp only [d828, d28880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d829 q = 1) (hb : d202304 q = 1) : d28881 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d829, d28881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25761 q = 1) (hb : d251389 q = 1) : d251925 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25761, d251389, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25761, d251389, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25762 q = 1) (hb : d251389 q = 1) : d251926 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25762, d251926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25762, d251926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25763 q = 1) (hb : d251389 q = 1) : d251927 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25763, d251927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25763, d251927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25428 q = 1) (hb : d251389 q = 1) : d251673 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d25767 q = 1) (hb : d251389 q = 1) : d25767 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25768 q = 1) (hb : d251389 q = 1) : d251928 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25768, d251928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25768, d251928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25769 q = 1) (hb : d251389 q = 1) : d251929 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25769, d251929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25769, d251929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h17 (q : Pattern) (ha : d25770 q = 1) (hb : d251389 q = 1) : d251930 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25770, d251930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25770, d251930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro62979 (p : Pattern) (ha : d25775 p = 1) (hb : d251389 p = 1) : d251935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25428 q = 1) (hb : d251389 q = 1) : d251673 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d537 q = 1) (hb : d202304 q = 1) : d30971 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48018 q ha hb
    | true =>
      simp only [d537, d30971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d538 q = 1) (hb : d202304 q = 1) : d30972 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d538, d30972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25429 q = 1) (hb : d251389 q = 1) : d251674 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, d251389, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25429, d251389, d251674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25430 q = 1) (hb : d251389 q = 1) : d251675 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d251675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25430, d251675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25431 q = 1) (hb : d251389 q = 1) : d251676 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d251676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25431, d251676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d25449 q = 1) (hb : d251389 q = 1) : d251688 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d25450 q = 1) (hb : d251389 q = 1) : d251689 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d25775 q = 1) (hb : d251389 q = 1) : d251935 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25775, d251935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25775, d251935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62980 (p : Pattern) (ha : d25783 p = 1) (hb : d251389 p = 1) : d251943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d202304 q = 1) : d30967 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48017 q ha hb
    | true =>
      simp only [d531, d30967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d30968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25428 q = 1) (hb : d251389 q = 1) : d251673 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25428, d251389, d251673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25781 q = 1) (hb : d251389 q = 1) : d251941 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25781, d251941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25781, d251941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25782 q = 1) (hb : d251389 q = 1) : d251942 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25782, d251942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25782, d251942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d313 q = 1) (hb : d202304 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47966 q ha hb
    | true =>
      simp only [d313, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d314 q = 1) (hb : d202304 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d314, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25210 q = 1) (hb : d251389 q = 1) : d251498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25210, d251389, d251498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d25449 q = 1) (hb : d251389 q = 1) : d251688 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25449, d251688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d25450 q = 1) (hb : d251389 q = 1) : d251689 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25450, d251689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d25783 q = 1) (hb : d251389 q = 1) : d251943 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25783, d251943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25783, d251943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro62981 (p : Pattern) (ha : d25789 p = 1) (hb : d251389 p = 1) : d251949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25771 q = 1) (hb : d251389 q = 1) : d251931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d251931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62978 q ha hb
    | true =>
      simp only [d25771, d251931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25772 q = 1) (hb : d251389 q = 1) : d251932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d251932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25772, d251932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25773 q = 1) (hb : d251389 q = 1) : d251933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25773, d251933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25773, d251933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25774 q = 1) (hb : d251389 q = 1) : d251934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25774, d251934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25774, d251934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25776 q = 1) (hb : d251389 q = 1) : d251936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d251936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62979 q ha hb
    | true =>
      simp only [d25776, d251936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25777 q = 1) (hb : d251389 q = 1) : d251937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d251937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25777, d251937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25778 q = 1) (hb : d251389 q = 1) : d251938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25778, d251938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25778, d251938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25779 q = 1) (hb : d251389 q = 1) : d251939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25779, d251939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25779, d251939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25780 q = 1) (hb : d251389 q = 1) : d251940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25780, d251940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25780, d251940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25784 q = 1) (hb : d251389 q = 1) : d251944 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25784, d251944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62980 q ha hb
    | true =>
      simp only [d25784, d251944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25785 q = 1) (hb : d251389 q = 1) : d251945 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25785, d251945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25785, d251945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25786 q = 1) (hb : d251389 q = 1) : d251946 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25786, d251946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25786, d251946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25787 q = 1) (hb : d251389 q = 1) : d251947 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25787, d251947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25787, d251947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25454 q = 1) (hb : d251389 q = 1) : d251693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25455 q = 1) (hb : d251389 q = 1) : d251694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25788 q = 1) (hb : d251389 q = 1) : d251948 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25788, d251948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25788, d251948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25789 q = 1) (hb : d251389 q = 1) : d251949 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25789, d251949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25789, d251949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62982 (p : Pattern) (ha : d25793 p = 1) (hb : d251389 p = 1) : d251953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25454 q = 1) (hb : d251389 q = 1) : d251693 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25454, d251693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25455 q = 1) (hb : d251389 q = 1) : d251694 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25455, d251694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25693 q = 1) (hb : d251389 q = 1) : d251856 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d251856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25694 q = 1) (hb : d251389 q = 1) : d251857 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25694, d251857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25695 q = 1) (hb : d251389 q = 1) : d251858 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d251858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25695, d251858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25698 q = 1) (hb : d251389 q = 1) : d251861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25698, d251861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25793 q = 1) (hb : d251389 q = 1) : d251953 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25793, d251953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25793, d251953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62983 (p : Pattern) (ha : d25799 p = 1) (hb : d251389 p = 1) : d251959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25790 q = 1) (hb : d251389 q = 1) : d251950 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25790, d251950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62981 q ha hb
    | true =>
      simp only [d25790, d251950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62955 q ha hb
  have h2 (q : Pattern) (ha : d25791 q = 1) (hb : d251389 q = 1) : d251951 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25791, d251951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25791, d251951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25792 q = 1) (hb : d251389 q = 1) : d251952 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25792, d251952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25792, d251952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25794 q = 1) (hb : d251389 q = 1) : d251954 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25794, d251954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62955 q ha hb
    | true =>
      simp only [d25794, d251954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62982 q ha hb
  have h5 (q : Pattern) (ha : d25795 q = 1) (hb : d251389 q = 1) : d251955 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25795, d251955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25795, d251955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25796 q = 1) (hb : d251389 q = 1) : d251956 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25796, d251956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25796, d251956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25797 q = 1) (hb : d251389 q = 1) : d251957 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25797, d251957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25797, d251957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25700 q = 1) (hb : d251389 q = 1) : d251863 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d251863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62955 q ha hb
    | true =>
      simp only [d25700, d251863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62956 q ha hb
  have h9 (q : Pattern) (ha : d25701 q = 1) (hb : d251389 q = 1) : d251864 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d251864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d251864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25702 q = 1) (hb : d251389 q = 1) : d251865 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d251865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d251865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25704 q = 1) (hb : d251389 q = 1) : d251867 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62956 q ha hb
    | true =>
      simp only [d25704, d251867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62957 q ha hb
  have h12 (q : Pattern) (ha : d25705 q = 1) (hb : d251389 q = 1) : d251868 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d251868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25706 q = 1) (hb : d251389 q = 1) : d251869 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d251869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25707 q = 1) (hb : d251389 q = 1) : d251870 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d251870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25707, d251870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25798 q = 1) (hb : d251389 q = 1) : d251958 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25798, d251958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25798, d251958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25799 q = 1) (hb : d251389 q = 1) : d251959 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25799, d251959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25799, d251959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62984 (p : Pattern) (ha : d25805 p = 1) (hb : d251389 p = 1) : d251965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d251389 q = 1) : d251960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d251960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62983 q ha hb
    | true =>
      simp only [d25800, d251960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d251389 q = 1) : d251961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d251961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d251961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d251389 q = 1) : d251962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d251962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d251962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d251389 q = 1) : d251963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d251963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d251963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d251389 q = 1) : d251964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d251964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d251964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25805 q = 1) (hb : d251389 q = 1) : d251965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25805, d251965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25805, d251965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62985 (p : Pattern) (ha : d25875 p = 1) (hb : d251389 p = 1) : d251971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d251389 q = 1) : d251968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d251968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d251968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d251389 q = 1) : d251969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d251969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d251969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d251389 q = 1) : d251970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d251970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d251970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25875 q = 1) (hb : d251389 q = 1) : d251971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25875, d251971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25875, d251971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62986 (p : Pattern) (ha : d202094 p = 1) (hb : d251389 p = 1) : d251977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d251389 q = 1) : d251911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d251911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62974 q ha hb
    | true =>
      simp only [d25748, d251911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62975 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d251389 q = 1) : d251912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d251912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d251912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d251389 q = 1) : d251913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d251913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d251913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d251389 q = 1) : d251914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d251914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d251914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d251389 q = 1) : d251921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d251921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62976 q ha hb
    | true =>
      simp only [d25758, d251921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62977 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d251389 q = 1) : d251922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d251922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d251922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d251389 q = 1) : d251923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d251923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d251923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d251389 q = 1) : d251966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d251966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62984 q ha hb
    | true =>
      simp only [d25806, d251966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62960 q ha hb
  have h9 (q : Pattern) (ha : d202090 q = 1) (hb : d251389 q = 1) : d251967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d251967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202090, d251967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d251389 q = 1) : d251972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d251972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62985 q ha hb
    | true =>
      simp only [d25876, d251972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d251389 q = 1) : d251973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d251973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d251973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202091 q = 1) (hb : d251389 q = 1) : d251974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d251974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d251974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202092 q = 1) (hb : d251389 q = 1) : d251975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d251975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202092, d251975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202093 q = 1) (hb : d251389 q = 1) : d251976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d251976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202093, d251976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202094 q = 1) (hb : d251389 q = 1) : d251977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d251977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202094, d251977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62987 (p : Pattern) (ha : d25882 p = 1) (hb : d251389 p = 1) : d251978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d251389 q = 1) : d251881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d251881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d251389 q = 1) : d251907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d251907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d251907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25882 q = 1) (hb : d251389 q = 1) : d251978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25882, d251978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25882, d251978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62988 (p : Pattern) (ha : d25883 p = 1) (hb : d251389 p = 1) : d251979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d251389 q = 1) : d251885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d251885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d251389 q = 1) : d251909 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d251909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d251909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25883 q = 1) (hb : d251389 q = 1) : d251979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25883, d251979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25883, d251979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62989 (p : Pattern) (ha : d25888 p = 1) (hb : d251389 p = 1) : d251984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d251389 q = 1) : d251880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d251880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d251389 q = 1) : d251915 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d251915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d251915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d251389 q = 1) : d251916 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d251916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d251916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25888 q = 1) (hb : d251389 q = 1) : d251984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25888, d251984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25888, d251984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62990 (p : Pattern) (ha : d25889 p = 1) (hb : d251389 p = 1) : d251985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d251389 q = 1) : d251878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62959 q ha hb
    | true =>
      simp only [d25715, d251878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d251389 q = 1) : d251879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d251879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d251389 q = 1) : d251884 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d251884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d251389 q = 1) : d251918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d251918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d251918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d251389 q = 1) : d251919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d251919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d251919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25889 q = 1) (hb : d251389 q = 1) : d251985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25889, d251985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25889, d251985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62991 (p : Pattern) (ha : d25893 p = 1) (hb : d251389 p = 1) : d251989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d251389 q = 1) : d251960 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d251960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62983 q ha hb
    | true =>
      simp only [d25800, d251960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d251389 q = 1) : d251961 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d251961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d251961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d251389 q = 1) : d251962 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d251962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d251962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d251389 q = 1) : d251963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d251963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d251963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d251389 q = 1) : d251964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d251964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d251964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25893 q = 1) (hb : d251389 q = 1) : d251989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25893, d251989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25893, d251989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62992 (p : Pattern) (ha : d25899 p = 1) (hb : d251389 p = 1) : d251992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d251389 q = 1) : d251874 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62958 q ha hb
    | true =>
      simp only [d25711, d251874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d251389 q = 1) : d251875 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d251875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d251389 q = 1) : d251968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d251968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d251968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d251389 q = 1) : d251969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d251969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d251969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d251389 q = 1) : d251970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d251970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d251970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25899 q = 1) (hb : d251389 q = 1) : d251992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25899, d251992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25899, d251992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62993 (p : Pattern) (ha : d202099 p = 1) (hb : d251389 p = 1) : d251998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d251389 q = 1) : d251911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d251911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62974 q ha hb
    | true =>
      simp only [d25748, d251911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62975 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d251389 q = 1) : d251912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d251912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d251912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d251389 q = 1) : d251913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d251913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d251913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d251389 q = 1) : d251914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d251914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d251914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d251389 q = 1) : d251921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d251921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62976 q ha hb
    | true =>
      simp only [d25758, d251921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62977 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d251389 q = 1) : d251922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d251922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d251922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d251389 q = 1) : d251923 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d251923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d251923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d251389 q = 1) : d251966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d251966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62984 q ha hb
    | true =>
      simp only [d25806, d251966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62960 q ha hb
  have h9 (q : Pattern) (ha : d202090 q = 1) (hb : d251389 q = 1) : d251967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d251967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202090, d251967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d251389 q = 1) : d251972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d251972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62985 q ha hb
    | true =>
      simp only [d25876, d251972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d251389 q = 1) : d251973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d251973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d251973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202091 q = 1) (hb : d251389 q = 1) : d251974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d251974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d251974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202092 q = 1) (hb : d251389 q = 1) : d251975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d251975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202092, d251975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202093 q = 1) (hb : d251389 q = 1) : d251976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d251976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202093, d251976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25884 q = 1) (hb : d251389 q = 1) : d251980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25884, d251980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62987 q ha hb
    | true =>
      simp only [d25884, d251980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62988 q ha hb
  have h16 (q : Pattern) (ha : d25885 q = 1) (hb : d251389 q = 1) : d251981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25885, d251981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25885, d251981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25886 q = 1) (hb : d251389 q = 1) : d251982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25886, d251982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25886, d251982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25887 q = 1) (hb : d251389 q = 1) : d251983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25887, d251983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25887, d251983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25890 q = 1) (hb : d251389 q = 1) : d251986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25890, d251986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62989 q ha hb
    | true =>
      simp only [d25890, d251986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62990 q ha hb
  have h20 (q : Pattern) (ha : d25891 q = 1) (hb : d251389 q = 1) : d251987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25891, d251987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25891, d251987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25892 q = 1) (hb : d251389 q = 1) : d251988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25892, d251988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25892, d251988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25894 q = 1) (hb : d251389 q = 1) : d251990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d251990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62991 q ha hb
    | true =>
      simp only [d25894, d251990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62963 q ha hb
  have h23 (q : Pattern) (ha : d202095 q = 1) (hb : d251389 q = 1) : d251991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d251991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202095, d251991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25900 q = 1) (hb : d251389 q = 1) : d251993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d251993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62992 q ha hb
    | true =>
      simp only [d25900, d251993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25901 q = 1) (hb : d251389 q = 1) : d251994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d251994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25901, d251994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202096 q = 1) (hb : d251389 q = 1) : d251995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d251995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202096, d251995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202097 q = 1) (hb : d251389 q = 1) : d251996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d251996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202097, d251996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202098 q = 1) (hb : d251389 q = 1) : d251997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d251997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202098, d251997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202099 q = 1) (hb : d251389 q = 1) : d251998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d251998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202099, d251998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62994 (p : Pattern) (ha : d202106 p = 1) (hb : d251389 p = 1) : d252018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25894 q = 1) (hb : d251389 q = 1) : d251990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d251990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62991 q ha hb
    | true =>
      simp only [d25894, d251990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62963 q ha hb
  have h2 (q : Pattern) (ha : d202095 q = 1) (hb : d251389 q = 1) : d251991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d251991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202095, d251991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25900 q = 1) (hb : d251389 q = 1) : d251993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d251993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62992 q ha hb
    | true =>
      simp only [d25900, d251993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25901 q = 1) (hb : d251389 q = 1) : d251994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d251994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25901, d251994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202096 q = 1) (hb : d251389 q = 1) : d251995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d251995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202096, d251995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202104 q = 1) (hb : d251389 q = 1) : d252016 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d252016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202104, d252016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202105 q = 1) (hb : d251389 q = 1) : d252017 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d252017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202105, d252017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202106 q = 1) (hb : d251389 q = 1) : d252018 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d252018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202106, d252018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62995 (p : Pattern) (ha : d25947 p = 1) (hb : d251389 p = 1) : d252040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25933 q = 1) (hb : d251389 q = 1) : d252026 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25933, d252026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25933, d252026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62978 q ha hb
  have h2 (q : Pattern) (ha : d25771 q = 1) (hb : d251389 q = 1) : d251931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d251931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62978 q ha hb
    | true =>
      simp only [d25771, d251931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25934 q = 1) (hb : d251389 q = 1) : d252027 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25934, d252027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25934, d252027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25772 q = 1) (hb : d251389 q = 1) : d251932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d251932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25772, d251932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25935 q = 1) (hb : d251389 q = 1) : d252028 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25935, d252028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25935, d252028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25936 q = 1) (hb : d251389 q = 1) : d252029 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25936, d252029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25936, d252029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25937 q = 1) (hb : d251389 q = 1) : d252030 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25937, d252030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25937, d252030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62979 q ha hb
  have h8 (q : Pattern) (ha : d25776 q = 1) (hb : d251389 q = 1) : d251936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d251936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62979 q ha hb
    | true =>
      simp only [d25776, d251936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25938 q = 1) (hb : d251389 q = 1) : d252031 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25938, d252031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25938, d252031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25777 q = 1) (hb : d251389 q = 1) : d251937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d251937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25777, d251937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25939 q = 1) (hb : d251389 q = 1) : d252032 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25939, d252032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25939, d252032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25940 q = 1) (hb : d251389 q = 1) : d252033 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25940, d252033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25940, d252033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25941 q = 1) (hb : d251389 q = 1) : d252034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25941, d252034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25941, d252034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25942 q = 1) (hb : d251389 q = 1) : d252035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25942, d252035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25942, d252035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62980 q ha hb
  have h15 (q : Pattern) (ha : d25784 q = 1) (hb : d251389 q = 1) : d251944 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25784, d251944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62980 q ha hb
    | true =>
      simp only [d25784, d251944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25943 q = 1) (hb : d251389 q = 1) : d252036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25943, d252036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25943, d252036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25785 q = 1) (hb : d251389 q = 1) : d251945 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25785, d251945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25785, d251945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25944 q = 1) (hb : d251389 q = 1) : d252037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25944, d252037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25944, d252037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25945 q = 1) (hb : d251389 q = 1) : d252038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25945, d252038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25945, d252038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25586 q = 1) (hb : d251389 q = 1) : d251782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
  have h21 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25587 q = 1) (hb : d251389 q = 1) : d251783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25588 q = 1) (hb : d251389 q = 1) : d251784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25589 q = 1) (hb : d251389 q = 1) : d251785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25946 q = 1) (hb : d251389 q = 1) : d252039 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25946, d252039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25946, d252039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25947 q = 1) (hb : d251389 q = 1) : d252040 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25947, d252040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25947, d252040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro62996 (p : Pattern) (ha : d25953 p = 1) (hb : d251389 p = 1) : d252046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d251389 q = 1) : d251773 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d251773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d251773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d251389 q = 1) : d251678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62927 q ha hb
    | true =>
      simp only [d25439, d251678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d251389 q = 1) : d251774 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d251774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d251774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d251389 q = 1) : d251679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d251679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d251389 q = 1) : d251775 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d251775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d251775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d251389 q = 1) : d251776 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d251776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d251776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d251389 q = 1) : d251777 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d251777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d251777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d251389 q = 1) : d251683 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62928 q ha hb
    | true =>
      simp only [d25444, d251683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d251389 q = 1) : d251778 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d251778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d251778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d251389 q = 1) : d251684 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d251684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d251389 q = 1) : d251779 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d251779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d251779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d251389 q = 1) : d251780 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d251780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d251780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d251389 q = 1) : d251781 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d251781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d251781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25586 q = 1) (hb : d251389 q = 1) : d251782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
  have h15 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d25587 q = 1) (hb : d251389 q = 1) : d251783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25588 q = 1) (hb : d251389 q = 1) : d251784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25589 q = 1) (hb : d251389 q = 1) : d251785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d25948 q = 1) (hb : d251389 q = 1) : d252041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
  have h21 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25949 q = 1) (hb : d251389 q = 1) : d252042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25950 q = 1) (hb : d251389 q = 1) : d252043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d25951 q = 1) (hb : d251389 q = 1) : d252044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d25952 q = 1) (hb : d251389 q = 1) : d252045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25952, d252045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25952, d252045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d25953 q = 1) (hb : d251389 q = 1) : d252046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25953, d252046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25953, d252046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro62997 (p : Pattern) (ha : d25958 p = 1) (hb : d251389 p = 1) : d252051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25586 q = 1) (hb : d251389 q = 1) : d251782 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25586, d251782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
  have h2 (q : Pattern) (ha : d25452 q = 1) (hb : d251389 q = 1) : d251691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62929 q ha hb
    | true =>
      simp only [d25452, d251691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25587 q = 1) (hb : d251389 q = 1) : d251783 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25587, d251783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25453 q = 1) (hb : d251389 q = 1) : d251692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25453, d251692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25588 q = 1) (hb : d251389 q = 1) : d251784 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25588, d251784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25589 q = 1) (hb : d251389 q = 1) : d251785 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25589, d251785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25948 q = 1) (hb : d251389 q = 1) : d252041 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d252041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
  have h8 (q : Pattern) (ha : d25691 q = 1) (hb : d251389 q = 1) : d251854 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62954 q ha hb
    | true =>
      simp only [d25691, d251854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25949 q = 1) (hb : d251389 q = 1) : d252042 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25949, d252042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25692 q = 1) (hb : d251389 q = 1) : d251855 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25692, d251855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25950 q = 1) (hb : d251389 q = 1) : d252043 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25950, d252043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25951 q = 1) (hb : d251389 q = 1) : d252044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25951, d252044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25952 q = 1) (hb : d251389 q = 1) : d252045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25952, d252045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25952, d252045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25957 q = 1) (hb : d251389 q = 1) : d252050 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25957, d252050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25958 q = 1) (hb : d251389 q = 1) : d252051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25958, d252051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25958, d252051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62998 (p : Pattern) (ha : d25974 p = 1) (hb : d251389 p = 1) : d252067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25954 q = 1) (hb : d251389 q = 1) : d252047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25954, d252047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62995 q ha hb
    | true =>
      simp only [d25954, d252047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62996 q ha hb
  have h2 (q : Pattern) (ha : d25955 q = 1) (hb : d251389 q = 1) : d252048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25955, d252048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25955, d252048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25956 q = 1) (hb : d251389 q = 1) : d252049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25956, d252049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25956, d252049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25959 q = 1) (hb : d251389 q = 1) : d252052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25959, d252052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62996 q ha hb
    | true =>
      simp only [d25959, d252052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62997 q ha hb
  have h5 (q : Pattern) (ha : d25960 q = 1) (hb : d251389 q = 1) : d252053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25960, d252053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25960, d252053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25961 q = 1) (hb : d251389 q = 1) : d252054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25961, d252054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25961, d252054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25962 q = 1) (hb : d251389 q = 1) : d252055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25962, d252055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25962, d252055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25965 q = 1) (hb : d251389 q = 1) : d252058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d252058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62996 q ha hb
    | true =>
      simp only [d25965, d252058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62969 q ha hb
  have h9 (q : Pattern) (ha : d25966 q = 1) (hb : d251389 q = 1) : d252059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d252059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d252059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25967 q = 1) (hb : d251389 q = 1) : d252060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d252060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d252060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25969 q = 1) (hb : d251389 q = 1) : d252062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62969 q ha hb
    | true =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62970 q ha hb
  have h12 (q : Pattern) (ha : d25970 q = 1) (hb : d251389 q = 1) : d252063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25971 q = 1) (hb : d251389 q = 1) : d252064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25972 q = 1) (hb : d251389 q = 1) : d252065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d252065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25972, d252065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25973 q = 1) (hb : d251389 q = 1) : d252066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25973, d252066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25973, d252066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25974 q = 1) (hb : d251389 q = 1) : d252067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25974, d252067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25974, d252067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62999 (p : Pattern) (ha : d25979 p = 1) (hb : d251389 p = 1) : d252072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d251389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25965 q = 1) (hb : d251389 q = 1) : d252058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d252058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62996 q ha hb
    | true =>
      simp only [d25965, d252058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62969 q ha hb
  have h2 (q : Pattern) (ha : d25966 q = 1) (hb : d251389 q = 1) : d252059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d252059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d252059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25967 q = 1) (hb : d251389 q = 1) : d252060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d252060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d252060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25969 q = 1) (hb : d251389 q = 1) : d252062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62969 q ha hb
    | true =>
      simp only [d25969, d252062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62970 q ha hb
  have h5 (q : Pattern) (ha : d25970 q = 1) (hb : d251389 q = 1) : d252063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d252063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25971 q = 1) (hb : d251389 q = 1) : d252064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d252064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25972 q = 1) (hb : d251389 q = 1) : d252065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d252065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25972, d252065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25977 q = 1) (hb : d251389 q = 1) : d252070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d252070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25977, d252070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25978 q = 1) (hb : d251389 q = 1) : d252071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25978, d252071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25978, d252071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25979 q = 1) (hb : d251389 q = 1) : d252072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25979, d252072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25979, d252072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
