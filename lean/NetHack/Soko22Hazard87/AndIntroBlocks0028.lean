import NetHack.Soko22Hazard87.AndIntroBlocks0027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro7000 (p : Pattern) (ha : d67865 p = 1) (hb : d68222 p = 1) : d68696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4071 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4071 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4072 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67844 q = 1) (hb : d68222 q = 1) : d68684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67844, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6998 q ha hb
    | true =>
      simp only [d67844, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6999 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4073 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4074 q ha hb
  have h8 (q : Pattern) (ha : d67845 q = 1) (hb : d68222 q = 1) : d68685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67845, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67845, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67846 q = 1) (hb : d68222 q = 1) : d68686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67846, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67846, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d67847 q = 1) (hb : d68222 q = 1) : d68687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67847, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67847, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67851 q = 1) (hb : d68222 q = 1) : d67851 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4075 q ha hb
  have h13 (q : Pattern) (ha : d67852 q = 1) (hb : d68222 q = 1) : d68688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67852, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67852, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67853 q = 1) (hb : d68222 q = 1) : d68689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67853, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67853, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d67854 q = 1) (hb : d68222 q = 1) : d68690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67854, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67854, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67855 q = 1) (hb : d68222 q = 1) : d68691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67855, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67855, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d67860 q = 1) (hb : d68222 q = 1) : d67860 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4076 q ha hb
  have h19 (q : Pattern) (ha : d67861 q = 1) (hb : d68222 q = 1) : d68692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67861, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67861, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d67862 q = 1) (hb : d68222 q = 1) : d68693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67862, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d67862, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d67863 q = 1) (hb : d68222 q = 1) : d68694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67863, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67863, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67864 q = 1) (hb : d68222 q = 1) : d68695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67864, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67864, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67865 q = 1) (hb : d68222 q = 1) : d68696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67865, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d67865, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro7001 (p : Pattern) (ha : d67871 p = 1) (hb : d68222 p = 1) : d68702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67866 q = 1) (hb : d68222 q = 1) : d68697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67866, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67866, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7000 q ha hb
  have h2 (q : Pattern) (ha : d67867 q = 1) (hb : d68222 q = 1) : d68698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67867, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67867, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67868 q = 1) (hb : d68222 q = 1) : d68699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67868, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67868, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67869 q = 1) (hb : d68222 q = 1) : d68700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67869, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67869, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67870 q = 1) (hb : d68222 q = 1) : d68701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67870, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67870, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67871 q = 1) (hb : d68222 q = 1) : d68702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67871, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67871, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7002 (p : Pattern) (ha : d67877 p = 1) (hb : d68222 p = 1) : d68708 p = 1 := by
  have h0 (q : Pattern) (ha : d67718 q = 1) (hb : d68222 q = 1) : d68601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67718, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6981 q ha hb
    | true =>
      simp only [d67718, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6985 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67755 q = 1) (hb : d68222 q = 1) : d68625 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67755, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67755, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6989 q ha hb
  have h3 (q : Pattern) (ha : d67756 q = 1) (hb : d68222 q = 1) : d68626 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67756, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67756, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67793 q = 1) (hb : d68222 q = 1) : d68650 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67793, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67793, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6993 q ha hb
  have h5 (q : Pattern) (ha : d67794 q = 1) (hb : d68222 q = 1) : d68651 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67794, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67794, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67795 q = 1) (hb : d68222 q = 1) : d68652 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67795, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67795, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67832 q = 1) (hb : d68222 q = 1) : d68676 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67832, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67832, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6997 q ha hb
  have h8 (q : Pattern) (ha : d67833 q = 1) (hb : d68222 q = 1) : d68677 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67833, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67833, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67834 q = 1) (hb : d68222 q = 1) : d68678 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67834, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67834, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67835 q = 1) (hb : d68222 q = 1) : d68679 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67835, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67835, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67872 q = 1) (hb : d68222 q = 1) : d68703 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67872, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67872, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7001 q ha hb
  have h12 (q : Pattern) (ha : d67873 q = 1) (hb : d68222 q = 1) : d68704 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67873, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67873, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67874 q = 1) (hb : d68222 q = 1) : d68705 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67874, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67874, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67875 q = 1) (hb : d68222 q = 1) : d68706 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67875, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67875, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67876 q = 1) (hb : d68222 q = 1) : d68707 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67876, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67876, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67877 q = 1) (hb : d68222 q = 1) : d68708 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67877, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67877, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7003 (p : Pattern) (ha : d67883 p = 1) (hb : d68222 p = 1) : d68714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67878 q = 1) (hb : d68222 q = 1) : d68709 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67878, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7002 q ha hb
    | true =>
      simp only [d67878, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67879 q = 1) (hb : d68222 q = 1) : d68710 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67879, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67879, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67880 q = 1) (hb : d68222 q = 1) : d68711 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67880, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67880, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67881 q = 1) (hb : d68222 q = 1) : d68712 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67881, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67881, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67882 q = 1) (hb : d68222 q = 1) : d68713 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67882, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67882, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67883 q = 1) (hb : d68222 q = 1) : d68714 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67883, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67883, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7004 (p : Pattern) (ha : d67889 p = 1) (hb : d68222 p = 1) : d68720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67884 q = 1) (hb : d68222 q = 1) : d68715 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67884, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7003 q ha hb
    | true =>
      simp only [d67884, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67885 q = 1) (hb : d68222 q = 1) : d68716 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67885, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67885, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67886 q = 1) (hb : d68222 q = 1) : d68717 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67886, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67886, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67887 q = 1) (hb : d68222 q = 1) : d68718 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67887, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67887, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67888 q = 1) (hb : d68222 q = 1) : d68719 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67888, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67888, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67889 q = 1) (hb : d68222 q = 1) : d68720 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67889, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67889, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7005 (p : Pattern) (ha : d67895 p = 1) (hb : d68222 p = 1) : d68726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67890 q = 1) (hb : d68222 q = 1) : d68721 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67890, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7004 q ha hb
    | true =>
      simp only [d67890, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67891 q = 1) (hb : d68222 q = 1) : d68722 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67891, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67891, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67892 q = 1) (hb : d68222 q = 1) : d68723 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67892, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67892, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67893 q = 1) (hb : d68222 q = 1) : d68724 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67893, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67893, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67894 q = 1) (hb : d68222 q = 1) : d68725 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67894, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67894, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67895 q = 1) (hb : d68222 q = 1) : d68726 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67895, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67895, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7006 (p : Pattern) (ha : d67901 p = 1) (hb : d68222 p = 1) : d68732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67896 q = 1) (hb : d68222 q = 1) : d68727 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67896, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7005 q ha hb
    | true =>
      simp only [d67896, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67897 q = 1) (hb : d68222 q = 1) : d68728 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67897, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67897, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67898 q = 1) (hb : d68222 q = 1) : d68729 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67898, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67898, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67899 q = 1) (hb : d68222 q = 1) : d68730 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67899, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67899, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67900 q = 1) (hb : d68222 q = 1) : d68731 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67900, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67900, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67901 q = 1) (hb : d68222 q = 1) : d68732 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67901, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67901, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7007 (p : Pattern) (ha : d67907 p = 1) (hb : d68222 p = 1) : d68738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67902 q = 1) (hb : d68222 q = 1) : d68733 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67902, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7006 q ha hb
    | true =>
      simp only [d67902, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67903 q = 1) (hb : d68222 q = 1) : d68734 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67903, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67903, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67904 q = 1) (hb : d68222 q = 1) : d68735 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67904, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67904, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67905 q = 1) (hb : d68222 q = 1) : d68736 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67905, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67905, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67906 q = 1) (hb : d68222 q = 1) : d68737 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67906, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67906, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67907 q = 1) (hb : d68222 q = 1) : d68738 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67907, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67907, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7008 (p : Pattern) (ha : d67913 p = 1) (hb : d68222 p = 1) : d68744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67908 q = 1) (hb : d68222 q = 1) : d68739 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67908, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7007 q ha hb
    | true =>
      simp only [d67908, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67909 q = 1) (hb : d68222 q = 1) : d68740 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67909, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67909, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67910 q = 1) (hb : d68222 q = 1) : d68741 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67910, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67910, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67911 q = 1) (hb : d68222 q = 1) : d68742 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67911, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67911, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67912 q = 1) (hb : d68222 q = 1) : d68743 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67912, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67912, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67913 q = 1) (hb : d68222 q = 1) : d68744 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67913, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67913, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7009 (p : Pattern) (ha : d67919 p = 1) (hb : d68222 p = 1) : d68750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67914 q = 1) (hb : d68222 q = 1) : d68745 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67914, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7008 q ha hb
    | true =>
      simp only [d67914, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67915 q = 1) (hb : d68222 q = 1) : d68746 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67915, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67915, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67916 q = 1) (hb : d68222 q = 1) : d68747 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67916, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67916, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67917 q = 1) (hb : d68222 q = 1) : d68748 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67917, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67917, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67918 q = 1) (hb : d68222 q = 1) : d68749 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67918, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67918, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67919 q = 1) (hb : d68222 q = 1) : d68750 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67919, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67919, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7010 (p : Pattern) (ha : d53859 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4170 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7011 (p : Pattern) (ha : d53865 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7010 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7012 (p : Pattern) (ha : d48 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d44, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d48 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7013 (p : Pattern) (ha : d55 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d44, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d45 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d51 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d51, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d52 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7014 (p : Pattern) (ha : d60 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7015 (p : Pattern) (ha : d89 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d86 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d86, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d87 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d88 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7016 (p : Pattern) (ha : d95 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7012 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7013 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7014 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7015 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7017 (p : Pattern) (ha : d67614 p = 1) (hb : d74857 p = 1) : d75449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d74857 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d74857 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4335, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d67611 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67612 q = 1) (hb : d74857 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67612, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67612, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67613 q = 1) (hb : d74857 q = 1) : d75448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67613, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67613, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67614 q = 1) (hb : d74857 q = 1) : d75449 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67614, d75449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67614, d75449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7018 (p : Pattern) (ha : d67618 p = 1) (hb : d74857 p = 1) : d75451 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d74857 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d74857 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4335 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4335, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67611 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67611, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67612 q = 1) (hb : d74857 q = 1) : d3843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67612, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67612, d3843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67613 q = 1) (hb : d74857 q = 1) : d75448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67613, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67613, d75448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198 q = 1) (hb : d74857 q = 1) : d198 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d202 q = 1) (hb : d74857 q = 1) : d202 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4340 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4340, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d67615 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67615, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67615, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d67616 q = 1) (hb : d74857 q = 1) : d3846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67616, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67616, d3846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67617 q = 1) (hb : d74857 q = 1) : d75450 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67617, d75450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67617, d75450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67618 q = 1) (hb : d74857 q = 1) : d75451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67618, d75451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67618, d75451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7019 (p : Pattern) (ha : d67625 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4340, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67615 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67615, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67615, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67623 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67624 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67625 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7020 (p : Pattern) (ha : d67634 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4355, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67631 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67631, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67632 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67633 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67634 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7021 (p : Pattern) (ha : d67640 p = 1) (hb : d74857 p = 1) : d75457 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d74857 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67619 q = 1) (hb : d74857 q = 1) : d75452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67619, d75452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7017 q ha hb
    | true =>
      simp only [d67619, d75452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7018 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d74857 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d67620 q = 1) (hb : d74857 q = 1) : d75453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67620, d75453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67620, d75453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67621 q = 1) (hb : d74857 q = 1) : d75454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67621, d75454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67621, d75454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67622 q = 1) (hb : d74857 q = 1) : d75455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67622, d75455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67622, d75455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67626 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7019 q ha hb
  have h8 (q : Pattern) (ha : d67627 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d67628 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d67629 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d67630 q = 1) (hb : d74857 q = 1) : d75456 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67630, d75456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67630, d75456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67635 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7020 q ha hb
  have h13 (q : Pattern) (ha : d67636 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d67637 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d67638 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d67639 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d67640 q = 1) (hb : d74857 q = 1) : d75457 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67640, d75457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67640, d75457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7022 (p : Pattern) (ha : d284 p = 1) (hb : d74857 p = 1) : d4693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d280 q = 1) (hb : d74856 q = 1) : d4689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d74857 q = 1) : d4690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d74857 q = 1) : d4691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d74857 q = 1) : d4692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284 q = 1) (hb : d74857 q = 1) : d4693 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7023 (p : Pattern) (ha : d291 p = 1) (hb : d74857 p = 1) : d4700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d280 q = 1) (hb : d74856 q = 1) : d4689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d74857 q = 1) : d4690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d74857 q = 1) : d4691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d74857 q = 1) : d4692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d287 q = 1) (hb : d74856 q = 1) : d4696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d74856, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d74856, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d288 q = 1) (hb : d74857 q = 1) : d4697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d74857, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d288, d74857, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d289 q = 1) (hb : d74857 q = 1) : d4698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d290 q = 1) (hb : d74857 q = 1) : d4699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d291 q = 1) (hb : d74857 q = 1) : d4700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d291, d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7024 (p : Pattern) (ha : d397 p = 1) (hb : d74857 p = 1) : d59651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d280 q = 1) (hb : d74856 q = 1) : d4689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d74856, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d74857 q = 1) : d4690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d281, d74857, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d74857 q = 1) : d4691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d74857 q = 1) : d4692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d74857 q = 1) : d103 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d397 q = 1) (hb : d74857 q = 1) : d59651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d59651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d397, d59651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7025 (p : Pattern) (ha : d67649 p = 1) (hb : d74857 p = 1) : d75465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d296 q = 1) : d296 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d297 q = 1) (hb : d58747 q = 1) : d4704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d298 q = 1) (hb : d74856 q = 1) : d4705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d74856, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d74856, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d299 q = 1) (hb : d74857 q = 1) : d4706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d74857, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d299, d74857, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d300 q = 1) (hb : d74857 q = 1) : d4707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d303 q = 1) : d303 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d304 q = 1) (hb : d58747 q = 1) : d4708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d305 q = 1) (hb : d74856 q = 1) : d4709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d74856, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d74856, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306 q = 1) (hb : d74857 q = 1) : d4710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d74857, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d306, d74857, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4371 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67646 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67646, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67646, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67647 q = 1) (hb : d74857 q = 1) : d75463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67647, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67647, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67648 q = 1) (hb : d74857 q = 1) : d75464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67648, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67648, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67649 q = 1) (hb : d74857 q = 1) : d75465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67649, d75465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67649, d75465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7026 (p : Pattern) (ha : d67653 p = 1) (hb : d74857 p = 1) : d75468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d296 q = 1) : d296 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d297 q = 1) (hb : d58747 q = 1) : d4704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d298 q = 1) (hb : d74856 q = 1) : d4705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d74856, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d74856, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d299 q = 1) (hb : d74857 q = 1) : d4706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d74857, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d299, d74857, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d300 q = 1) (hb : d74857 q = 1) : d4707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d303 q = 1) : d303 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d304 q = 1) (hb : d58747 q = 1) : d4708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d305 q = 1) (hb : d74856 q = 1) : d4709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d74856, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d74856, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306 q = 1) (hb : d74857 q = 1) : d4710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d74857, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d306, d74857, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4371 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4371, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67646 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67646, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67646, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67647 q = 1) (hb : d74857 q = 1) : d75463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67647, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67647, d75463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67648 q = 1) (hb : d74857 q = 1) : d75464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67648, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67648, d75464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d376 q = 1) : d376 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d194 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d377 q = 1) (hb : d58747 q = 1) : d4718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d58747, d4718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d377, d58747, d4718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d378 q = 1) (hb : d74856 q = 1) : d4719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d74856, d4719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378, d74856, d4719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d379 q = 1) (hb : d74857 q = 1) : d4720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d74857, d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d379, d74857, d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d380 q = 1) (hb : d74857 q = 1) : d4721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d381 q = 1) : d381 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d199 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d382 q = 1) (hb : d58747 q = 1) : d4722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d58747, d4722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d382, d58747, d4722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d383 q = 1) (hb : d74856 q = 1) : d4723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d74856, d4723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, d74856, d4723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d384 q = 1) (hb : d74857 q = 1) : d4724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d74857, d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d384, d74857, d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4376 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4376, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67650 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67650, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67650, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67651 q = 1) (hb : d74857 q = 1) : d75466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67651, d75466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67651, d75466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67652 q = 1) (hb : d74857 q = 1) : d75467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67652, d75467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67652, d75467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67653 q = 1) (hb : d74857 q = 1) : d75468 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67653, d75468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67653, d75468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7027 (p : Pattern) (ha : d67660 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4376 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4376, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67650 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67650, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67650, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67658 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67659 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67660 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7028 (p : Pattern) (ha : d67669 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4391 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4391, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67666 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67666, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67666, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67667 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67668 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67669 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7029 (p : Pattern) (ha : d67675 p = 1) (hb : d74857 p = 1) : d75474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d74857 q = 1) : d4694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7022 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d74857 q = 1) : d4695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d74857 q = 1) : d4701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7022 q ha hb
    | true =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7023 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d74857 q = 1) : d4702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d74857 q = 1) : d4703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67654 q = 1) (hb : d74857 q = 1) : d75469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67654, d75469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7025 q ha hb
    | true =>
      simp only [d67654, d75469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7026 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d74857 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d74857 q = 1) : d59652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d59652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7024 q ha hb
    | true =>
      simp only [d398, d59652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67655 q = 1) (hb : d74857 q = 1) : d75470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67655, d75470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67655, d75470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67656 q = 1) (hb : d74857 q = 1) : d75471 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67656, d75471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67656, d75471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67657 q = 1) (hb : d74857 q = 1) : d75472 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67657, d75472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67657, d75472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67661 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7027 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d74857 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67662 q = 1) (hb : d74857 q = 1) : d59656 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67662, d59656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67662, d59656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67663 q = 1) (hb : d74857 q = 1) : d59657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67663, d59657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67663, d59657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67664 q = 1) (hb : d74857 q = 1) : d59658 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67664, d59658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67664, d59658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67665 q = 1) (hb : d74857 q = 1) : d75473 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67665, d75473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67665, d75473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67670 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7028 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d74857 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67671 q = 1) (hb : d74857 q = 1) : d59660 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67671, d59660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67671, d59660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67672 q = 1) (hb : d74857 q = 1) : d59661 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67672, d59661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67672, d59661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67673 q = 1) (hb : d74857 q = 1) : d59662 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67673, d59662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67673, d59662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67674 q = 1) (hb : d74857 q = 1) : d59663 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67674, d59663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67674, d59663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67675 q = 1) (hb : d74857 q = 1) : d75474 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67675, d75474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67675, d75474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7030 (p : Pattern) (ha : d67681 p = 1) (hb : d74857 p = 1) : d75480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7016 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67641 q = 1) (hb : d74857 q = 1) : d75458 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67641, d75458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67641, d75458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7021 q ha hb
  have h6 (q : Pattern) (ha : d67642 q = 1) (hb : d74857 q = 1) : d75459 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67642, d75459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67642, d75459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67643 q = 1) (hb : d74857 q = 1) : d75460 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67643, d75460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67643, d75460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67644 q = 1) (hb : d74857 q = 1) : d75461 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67644, d75461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67644, d75461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67645 q = 1) (hb : d74857 q = 1) : d75462 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67645, d75462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67645, d75462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67676 q = 1) (hb : d74857 q = 1) : d75475 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67676, d75475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67676, d75475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7029 q ha hb
  have h11 (q : Pattern) (ha : d67677 q = 1) (hb : d74857 q = 1) : d75476 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67677, d75476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67677, d75476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67678 q = 1) (hb : d74857 q = 1) : d75477 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67678, d75477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67678, d75477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67679 q = 1) (hb : d74857 q = 1) : d75478 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67679, d75478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67679, d75478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67680 q = 1) (hb : d74857 q = 1) : d75479 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67680, d75479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67680, d75479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67681 q = 1) (hb : d74857 q = 1) : d75480 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67681, d75480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67681, d75480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7031 (p : Pattern) (ha : d497 p = 1) (hb : d74857 p = 1) : d4778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d487 q = 1) : d487 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d492 q = 1) (hb : d58747 q = 1) : d603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d493 q = 1) (hb : d74856 q = 1) : d4774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d74857 q = 1) : d4775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d74857 q = 1) : d4776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d74857 q = 1) : d4777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d497 q = 1) (hb : d74857 q = 1) : d4778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7032 (p : Pattern) (ha : d507 p = 1) (hb : d74857 p = 1) : d4785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d487 q = 1) : d487 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d492 q = 1) (hb : d58747 q = 1) : d603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d493 q = 1) (hb : d74856 q = 1) : d4774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d74857 q = 1) : d4775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d74857 q = 1) : d4776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d74857 q = 1) : d4777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d500 q = 1) : d500 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d502 q = 1) (hb : d58747 q = 1) : d626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d503 q = 1) (hb : d74856 q = 1) : d4781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d74856, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d74856, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d504 q = 1) (hb : d74857 q = 1) : d4782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d74857, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d504, d74857, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d505 q = 1) (hb : d74857 q = 1) : d4783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d506 q = 1) (hb : d74857 q = 1) : d4784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d507 q = 1) (hb : d74857 q = 1) : d4785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d507, d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7033 (p : Pattern) (ha : d638 p = 1) (hb : d74857 p = 1) : d59671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d487 q = 1) : d487 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d492 q = 1) (hb : d58747 q = 1) : d603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d493 q = 1) (hb : d74856 q = 1) : d4774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d74856, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d74857 q = 1) : d4775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d494, d74857, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d74857 q = 1) : d4776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d74857 q = 1) : d4777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d637 q = 1) (hb : d74857 q = 1) : d637 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d638 q = 1) (hb : d74857 q = 1) : d59671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, d59671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d638, d59671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7034 (p : Pattern) (ha : d67685 p = 1) (hb : d74857 p = 1) : d75483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d512 q = 1) : d512 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d515 q = 1) (hb : d58747 q = 1) : d4789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d516 q = 1) (hb : d74856 q = 1) : d4790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d74856, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d74856, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d517 q = 1) (hb : d74857 q = 1) : d4791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d74857, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d517, d74857, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d518 q = 1) (hb : d74857 q = 1) : d4792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d521 q = 1) : d521 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d525 q = 1) (hb : d58747 q = 1) : d4793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d526 q = 1) (hb : d74856 q = 1) : d4794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d74856, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d74856, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d527 q = 1) (hb : d74857 q = 1) : d4795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d74857, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d527, d74857, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4408 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4408, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67682 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67682, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67682, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67683 q = 1) (hb : d74857 q = 1) : d75481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67683, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67683, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67684 q = 1) (hb : d74857 q = 1) : d75482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67684, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67684, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67685 q = 1) (hb : d74857 q = 1) : d75483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67685, d75483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67685, d75483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7035 (p : Pattern) (ha : d67689 p = 1) (hb : d74857 p = 1) : d75486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d512 q = 1) : d512 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d515 q = 1) (hb : d58747 q = 1) : d4789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d516 q = 1) (hb : d74856 q = 1) : d4790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d74856, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d74856, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d517 q = 1) (hb : d74857 q = 1) : d4791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d74857, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d517, d74857, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d518 q = 1) (hb : d74857 q = 1) : d4792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d521 q = 1) : d521 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d525 q = 1) (hb : d58747 q = 1) : d4793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d526 q = 1) (hb : d74856 q = 1) : d4794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d74856, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d74856, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d527 q = 1) (hb : d74857 q = 1) : d4795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d74857, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d527, d74857, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4408 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4408, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67682 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67682, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67682, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67683 q = 1) (hb : d74857 q = 1) : d75481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67683, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67683, d75481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67684 q = 1) (hb : d74857 q = 1) : d75482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67684, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67684, d75482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d609 q = 1) : d609 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d610 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d611 q = 1) (hb : d58747 q = 1) : d4803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d58747, d4803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d611, d58747, d4803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d612 q = 1) (hb : d74856 q = 1) : d4804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d74856, d4804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d612, d74856, d4804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d613 q = 1) (hb : d74857 q = 1) : d4805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d74857, d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d613, d74857, d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d614 q = 1) (hb : d74857 q = 1) : d4806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d615 q = 1) : d615 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d616 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d617 q = 1) (hb : d58747 q = 1) : d4807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d58747, d4807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d617, d58747, d4807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d618 q = 1) (hb : d74856 q = 1) : d4808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d74856, d4808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, d74856, d4808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d619 q = 1) (hb : d74857 q = 1) : d4809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d74857, d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d619, d74857, d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4413 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4413, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67686 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67686, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67686, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67687 q = 1) (hb : d74857 q = 1) : d75484 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67687, d75484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67687, d75484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67688 q = 1) (hb : d74857 q = 1) : d75485 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67688, d75485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67688, d75485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67689 q = 1) (hb : d74857 q = 1) : d75486 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67689, d75486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67689, d75486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7036 (p : Pattern) (ha : d67696 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4413 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4413, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67686 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67686, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67686, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67694 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67695 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67696 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7037 (p : Pattern) (ha : d67705 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4428 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4428, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67702 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67702, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67702, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67703 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67704 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67705 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7038 (p : Pattern) (ha : d67711 p = 1) (hb : d74857 p = 1) : d75492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d74857 q = 1) : d4779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7031 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d74857 q = 1) : d4780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d74857 q = 1) : d4786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7031 q ha hb
    | true =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7032 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d74857 q = 1) : d4787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d74857 q = 1) : d4788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67690 q = 1) (hb : d74857 q = 1) : d75487 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67690, d75487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7034 q ha hb
    | true =>
      simp only [d67690, d75487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7035 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d74857 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d645 q = 1) (hb : d74857 q = 1) : d59672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d59672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7033 q ha hb
    | true =>
      simp only [d645, d59672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67691 q = 1) (hb : d74857 q = 1) : d75488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67691, d75488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67691, d75488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67692 q = 1) (hb : d74857 q = 1) : d75489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67692, d75489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67692, d75489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67693 q = 1) (hb : d74857 q = 1) : d75490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67693, d75490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67693, d75490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67697 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7036 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d74857 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67698 q = 1) (hb : d74857 q = 1) : d59676 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67698, d59676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67698, d59676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67699 q = 1) (hb : d74857 q = 1) : d59677 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67699, d59677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67699, d59677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67700 q = 1) (hb : d74857 q = 1) : d59678 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67700, d59678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67700, d59678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67701 q = 1) (hb : d74857 q = 1) : d75491 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67701, d75491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67701, d75491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67706 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7037 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d74857 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67707 q = 1) (hb : d74857 q = 1) : d59680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67707, d59680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67707, d59680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67708 q = 1) (hb : d74857 q = 1) : d59681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67708, d59681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67708, d59681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67709 q = 1) (hb : d74857 q = 1) : d59682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67709, d59682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67709, d59682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67710 q = 1) (hb : d74857 q = 1) : d59683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67710, d59683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67710, d59683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67711 q = 1) (hb : d74857 q = 1) : d75492 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67711, d75492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67711, d75492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7039 (p : Pattern) (ha : d67717 p = 1) (hb : d74857 p = 1) : d75498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67712 q = 1) (hb : d74857 q = 1) : d75493 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67712, d75493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67712, d75493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7038 q ha hb
  have h2 (q : Pattern) (ha : d67713 q = 1) (hb : d74857 q = 1) : d75494 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67713, d75494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67713, d75494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67714 q = 1) (hb : d74857 q = 1) : d75495 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67714, d75495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67714, d75495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67715 q = 1) (hb : d74857 q = 1) : d75496 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67715, d75496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67715, d75496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67716 q = 1) (hb : d74857 q = 1) : d75497 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67716, d75497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67716, d75497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67717 q = 1) (hb : d74857 q = 1) : d75498 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67717, d75498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67717, d75498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7040 (p : Pattern) (ha : d789 p = 1) (hb : d74857 p = 1) : d4873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d779 q = 1) : d779 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d784 q = 1) (hb : d58747 q = 1) : d909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d785 q = 1) (hb : d74856 q = 1) : d4869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d74857 q = 1) : d4870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d74857 q = 1) : d4871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d74857 q = 1) : d4872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d789 q = 1) (hb : d74857 q = 1) : d4873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7041 (p : Pattern) (ha : d799 p = 1) (hb : d74857 p = 1) : d4880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d779 q = 1) : d779 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d784 q = 1) (hb : d58747 q = 1) : d909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d785 q = 1) (hb : d74856 q = 1) : d4869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d74857 q = 1) : d4870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d74857 q = 1) : d4871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d74857 q = 1) : d4872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d792 q = 1) : d792 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d793 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d794 q = 1) (hb : d58747 q = 1) : d932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d795 q = 1) (hb : d74856 q = 1) : d4876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d74856, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d74856, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d796 q = 1) (hb : d74857 q = 1) : d4877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d74857, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d796, d74857, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d797 q = 1) (hb : d74857 q = 1) : d4878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d798 q = 1) (hb : d74857 q = 1) : d4879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d799 q = 1) (hb : d74857 q = 1) : d4880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d799, d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7042 (p : Pattern) (ha : d944 p = 1) (hb : d74857 p = 1) : d59692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d779 q = 1) : d779 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d784 q = 1) (hb : d58747 q = 1) : d909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d785 q = 1) (hb : d74856 q = 1) : d4869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d74856, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d74857 q = 1) : d4870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d786, d74857, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d74857 q = 1) : d4871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d74857 q = 1) : d4872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d943 q = 1) (hb : d74857 q = 1) : d943 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d944 q = 1) (hb : d74857 q = 1) : d59692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, d59692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d944, d59692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7043 (p : Pattern) (ha : d67722 p = 1) (hb : d74857 p = 1) : d75502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d804 q = 1) : d804 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d807 q = 1) (hb : d58747 q = 1) : d4884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d808 q = 1) (hb : d74856 q = 1) : d4885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d74856, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d74856, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d809 q = 1) (hb : d74857 q = 1) : d4886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d74857, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d809, d74857, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d810 q = 1) (hb : d74857 q = 1) : d4887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d813 q = 1) : d813 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d817 q = 1) (hb : d58747 q = 1) : d4888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d818 q = 1) (hb : d74856 q = 1) : d4889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d74856, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d74856, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d819 q = 1) (hb : d74857 q = 1) : d4890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d74857, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d819, d74857, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4446 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4446, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67719 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67719, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67719, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67720 q = 1) (hb : d74857 q = 1) : d75500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67720, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67720, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67721 q = 1) (hb : d74857 q = 1) : d75501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67721, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67721, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67722 q = 1) (hb : d74857 q = 1) : d75502 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67722, d75502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67722, d75502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7044 (p : Pattern) (ha : d67726 p = 1) (hb : d74857 p = 1) : d75505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d804 q = 1) : d804 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d807 q = 1) (hb : d58747 q = 1) : d4884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d808 q = 1) (hb : d74856 q = 1) : d4885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d74856, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d74856, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d809 q = 1) (hb : d74857 q = 1) : d4886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d74857, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d809, d74857, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d810 q = 1) (hb : d74857 q = 1) : d4887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d813 q = 1) : d813 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d817 q = 1) (hb : d58747 q = 1) : d4888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d818 q = 1) (hb : d74856 q = 1) : d4889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d74856, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d74856, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d819 q = 1) (hb : d74857 q = 1) : d4890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d74857, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d819, d74857, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4446 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4446, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67719 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67719, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67719, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67720 q = 1) (hb : d74857 q = 1) : d75500 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67720, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67720, d75500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67721 q = 1) (hb : d74857 q = 1) : d75501 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67721, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67721, d75501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d915 q = 1) : d915 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d916 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d917 q = 1) (hb : d58747 q = 1) : d4898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d58747, d4898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d917, d58747, d4898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d918 q = 1) (hb : d74856 q = 1) : d4899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d74856, d4899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d918, d74856, d4899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d919 q = 1) (hb : d74857 q = 1) : d4900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d74857, d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d919, d74857, d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d920 q = 1) (hb : d74857 q = 1) : d4901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d921 q = 1) : d921 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d922 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d923 q = 1) (hb : d58747 q = 1) : d4902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d58747, d4902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d923, d58747, d4902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d924 q = 1) (hb : d74856 q = 1) : d4903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d74856, d4903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, d74856, d4903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d925 q = 1) (hb : d74857 q = 1) : d4904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d74857, d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d925, d74857, d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4451 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4451, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67723 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67723, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67723, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67724 q = 1) (hb : d74857 q = 1) : d75503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67724, d75503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67724, d75503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67725 q = 1) (hb : d74857 q = 1) : d75504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67725, d75504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67725, d75504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67726 q = 1) (hb : d74857 q = 1) : d75505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67726, d75505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67726, d75505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7045 (p : Pattern) (ha : d67733 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4451 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4451, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67723 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67723, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67723, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67731 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67732 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67733 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7046 (p : Pattern) (ha : d67742 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4466, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67739 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67739, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67739, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67740 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67741 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67742 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7047 (p : Pattern) (ha : d67748 p = 1) (hb : d74857 p = 1) : d75511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d74857 q = 1) : d4874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7040 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d74857 q = 1) : d4875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d74857 q = 1) : d4881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7040 q ha hb
    | true =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7041 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d74857 q = 1) : d4882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d74857 q = 1) : d4883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67727 q = 1) (hb : d74857 q = 1) : d75506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67727, d75506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7043 q ha hb
    | true =>
      simp only [d67727, d75506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7044 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d74857 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d951 q = 1) (hb : d74857 q = 1) : d59693 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d59693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7042 q ha hb
    | true =>
      simp only [d951, d59693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67728 q = 1) (hb : d74857 q = 1) : d75507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67728, d75507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67728, d75507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67729 q = 1) (hb : d74857 q = 1) : d75508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67729, d75508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67729, d75508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67730 q = 1) (hb : d74857 q = 1) : d75509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67730, d75509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67730, d75509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67734 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7045 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d74857 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67735 q = 1) (hb : d74857 q = 1) : d59697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67735, d59697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67735, d59697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67736 q = 1) (hb : d74857 q = 1) : d59698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67736, d59698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67736, d59698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67737 q = 1) (hb : d74857 q = 1) : d59699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67737, d59699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67737, d59699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67738 q = 1) (hb : d74857 q = 1) : d75510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67738, d75510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67738, d75510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67743 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7046 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d74857 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67744 q = 1) (hb : d74857 q = 1) : d59701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67744, d59701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67744, d59701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67745 q = 1) (hb : d74857 q = 1) : d59702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67745, d59702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67745, d59702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67746 q = 1) (hb : d74857 q = 1) : d59703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67746, d59703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67746, d59703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67747 q = 1) (hb : d74857 q = 1) : d59704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67747, d59704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67747, d59704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67748 q = 1) (hb : d74857 q = 1) : d75511 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67748, d75511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67748, d75511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7048 (p : Pattern) (ha : d67754 p = 1) (hb : d74857 p = 1) : d75517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67749 q = 1) (hb : d74857 q = 1) : d75512 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67749, d75512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67749, d75512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7047 q ha hb
  have h2 (q : Pattern) (ha : d67750 q = 1) (hb : d74857 q = 1) : d75513 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67750, d75513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67750, d75513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67751 q = 1) (hb : d74857 q = 1) : d75514 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67751, d75514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67751, d75514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67752 q = 1) (hb : d74857 q = 1) : d75515 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67752, d75515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67752, d75515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67753 q = 1) (hb : d74857 q = 1) : d75516 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67753, d75516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67753, d75516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67754 q = 1) (hb : d74857 q = 1) : d75517 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67754, d75517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67754, d75517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7049 (p : Pattern) (ha : d1168 p = 1) (hb : d74857 p = 1) : d4969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1158 q = 1) : d1158 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1163 q = 1) (hb : d58747 q = 1) : d1320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1164 q = 1) (hb : d74856 q = 1) : d4965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d74857 q = 1) : d4966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d74857 q = 1) : d4967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d74857 q = 1) : d4968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1168 q = 1) (hb : d74857 q = 1) : d4969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7050 (p : Pattern) (ha : d1178 p = 1) (hb : d74857 p = 1) : d4976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1158 q = 1) : d1158 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1163 q = 1) (hb : d58747 q = 1) : d1320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1164 q = 1) (hb : d74856 q = 1) : d4965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d74857 q = 1) : d4966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d74857 q = 1) : d4967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d74857 q = 1) : d4968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1171 q = 1) : d1171 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1172 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1173 q = 1) (hb : d58747 q = 1) : d1343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d1174 q = 1) (hb : d74856 q = 1) : d4972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d74856, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d74856, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1175 q = 1) (hb : d74857 q = 1) : d4973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d74857, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1175, d74857, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1176 q = 1) (hb : d74857 q = 1) : d4974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1177 q = 1) (hb : d74857 q = 1) : d4975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1178 q = 1) (hb : d74857 q = 1) : d4976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1178, d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7051 (p : Pattern) (ha : d1355 p = 1) (hb : d74857 p = 1) : d59714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1158 q = 1) : d1158 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1163 q = 1) (hb : d58747 q = 1) : d1320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1164 q = 1) (hb : d74856 q = 1) : d4965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d74856, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d74857 q = 1) : d4966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1165, d74857, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d74857 q = 1) : d4967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d74857 q = 1) : d4968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1354 q = 1) (hb : d74857 q = 1) : d1354 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1355 q = 1) (hb : d74857 q = 1) : d59714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d59714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1355, d59714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7052 (p : Pattern) (ha : d67760 p = 1) (hb : d74857 p = 1) : d75522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1183 q = 1) : d1183 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1186 q = 1) (hb : d58747 q = 1) : d4980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1187 q = 1) (hb : d74856 q = 1) : d4981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d74856, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d74856, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1188 q = 1) (hb : d74857 q = 1) : d4982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d74857, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1188, d74857, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1189 q = 1) (hb : d74857 q = 1) : d4983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1192 q = 1) : d1192 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1196 q = 1) (hb : d58747 q = 1) : d4984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1197 q = 1) (hb : d74856 q = 1) : d4985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d74856, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d74856, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1198 q = 1) (hb : d74857 q = 1) : d4986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d74857, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1198, d74857, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4485 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4485, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67757 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67757, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67757, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67758 q = 1) (hb : d74857 q = 1) : d75520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67758, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67758, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67759 q = 1) (hb : d74857 q = 1) : d75521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67759, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67759, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67760 q = 1) (hb : d74857 q = 1) : d75522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67760, d75522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67760, d75522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7053 (p : Pattern) (ha : d67764 p = 1) (hb : d74857 p = 1) : d75525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1183 q = 1) : d1183 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1186 q = 1) (hb : d58747 q = 1) : d4980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1187 q = 1) (hb : d74856 q = 1) : d4981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d74856, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d74856, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1188 q = 1) (hb : d74857 q = 1) : d4982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d74857, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1188, d74857, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1189 q = 1) (hb : d74857 q = 1) : d4983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1192 q = 1) : d1192 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1196 q = 1) (hb : d58747 q = 1) : d4984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1197 q = 1) (hb : d74856 q = 1) : d4985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d74856, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d74856, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1198 q = 1) (hb : d74857 q = 1) : d4986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d74857, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1198, d74857, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4485 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4485, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67757 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67757, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67757, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67758 q = 1) (hb : d74857 q = 1) : d75520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67758, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67758, d75520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67759 q = 1) (hb : d74857 q = 1) : d75521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67759, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67759, d75521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d1326 q = 1) : d1326 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d1327 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d1328 q = 1) (hb : d58747 q = 1) : d4994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d58747, d4994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d1328, d58747, d4994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d1329 q = 1) (hb : d74856 q = 1) : d4995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d74856, d4995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1329, d74856, d4995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1330 q = 1) (hb : d74857 q = 1) : d4996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d74857, d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d1330, d74857, d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d1331 q = 1) (hb : d74857 q = 1) : d4997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d1332 q = 1) : d1332 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d1333 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d1334 q = 1) (hb : d58747 q = 1) : d4998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d58747, d4998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d1334, d58747, d4998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d1335 q = 1) (hb : d74856 q = 1) : d4999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d74856, d4999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, d74856, d4999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d1336 q = 1) (hb : d74857 q = 1) : d5000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d74857, d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d1336, d74857, d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4490 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67761 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67761, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67761, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67762 q = 1) (hb : d74857 q = 1) : d75523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67762, d75523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67762, d75523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67763 q = 1) (hb : d74857 q = 1) : d75524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67763, d75524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67763, d75524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67764 q = 1) (hb : d74857 q = 1) : d75525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67764, d75525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67764, d75525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7054 (p : Pattern) (ha : d67771 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4490, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67761 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67761, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67761, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67769 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67770 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67771 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7055 (p : Pattern) (ha : d67780 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4505, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67777 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67777, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67777, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67778 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67779 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67780 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7056 (p : Pattern) (ha : d67786 p = 1) (hb : d74857 p = 1) : d75531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d74857 q = 1) : d4970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7049 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d74857 q = 1) : d4971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d74857 q = 1) : d4977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7049 q ha hb
    | true =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7050 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d74857 q = 1) : d4978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d74857 q = 1) : d4979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67765 q = 1) (hb : d74857 q = 1) : d75526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67765, d75526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7052 q ha hb
    | true =>
      simp only [d67765, d75526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7053 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d74857 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1362 q = 1) (hb : d74857 q = 1) : d59715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d59715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7051 q ha hb
    | true =>
      simp only [d1362, d59715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67766 q = 1) (hb : d74857 q = 1) : d75527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67766, d75527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67766, d75527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67767 q = 1) (hb : d74857 q = 1) : d75528 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67767, d75528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67767, d75528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67768 q = 1) (hb : d74857 q = 1) : d75529 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67768, d75529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67768, d75529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67772 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7054 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d74857 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67773 q = 1) (hb : d74857 q = 1) : d59719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67773, d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67773, d59719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67774 q = 1) (hb : d74857 q = 1) : d59720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67774, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67774, d59720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67775 q = 1) (hb : d74857 q = 1) : d59721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67775, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67775, d59721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67776 q = 1) (hb : d74857 q = 1) : d75530 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67776, d75530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67776, d75530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67781 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7055 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d74857 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67782 q = 1) (hb : d74857 q = 1) : d59723 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67782, d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67782, d59723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67783 q = 1) (hb : d74857 q = 1) : d59724 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67783, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67783, d59724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67784 q = 1) (hb : d74857 q = 1) : d59725 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67784, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67784, d59725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67785 q = 1) (hb : d74857 q = 1) : d59726 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67785, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67785, d59726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67786 q = 1) (hb : d74857 q = 1) : d75531 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67786, d75531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67786, d75531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7057 (p : Pattern) (ha : d67792 p = 1) (hb : d74857 p = 1) : d75537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67787 q = 1) (hb : d74857 q = 1) : d75532 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67787, d75532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67787, d75532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7056 q ha hb
  have h2 (q : Pattern) (ha : d67788 q = 1) (hb : d74857 q = 1) : d75533 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67788, d75533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67788, d75533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67789 q = 1) (hb : d74857 q = 1) : d75534 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67789, d75534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67789, d75534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67790 q = 1) (hb : d74857 q = 1) : d75535 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67790, d75535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67790, d75535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67791 q = 1) (hb : d74857 q = 1) : d75536 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67791, d75536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67791, d75536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67792 q = 1) (hb : d74857 q = 1) : d75537 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67792, d75537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67792, d75537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7058 (p : Pattern) (ha : d1629 p = 1) (hb : d74857 p = 1) : d5080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1619 q = 1) : d1619 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1624 q = 1) (hb : d58747 q = 1) : d1797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1625 q = 1) (hb : d74856 q = 1) : d5076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d74857 q = 1) : d5077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d74857 q = 1) : d5078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d74857 q = 1) : d5079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1629 q = 1) (hb : d74857 q = 1) : d5080 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7059 (p : Pattern) (ha : d1639 p = 1) (hb : d74857 p = 1) : d5087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1619 q = 1) : d1619 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1624 q = 1) (hb : d58747 q = 1) : d1797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1625 q = 1) (hb : d74856 q = 1) : d5076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d74857 q = 1) : d5077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d74857 q = 1) : d5078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d74857 q = 1) : d5079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d1632 q = 1) : d1632 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1633 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1634 q = 1) (hb : d58747 q = 1) : d1820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d1635 q = 1) (hb : d74856 q = 1) : d5083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d74856, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d74856, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1636 q = 1) (hb : d74857 q = 1) : d5084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d74857, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1636, d74857, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d1637 q = 1) (hb : d74857 q = 1) : d5085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1638 q = 1) (hb : d74857 q = 1) : d5086 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1639 q = 1) (hb : d74857 q = 1) : d5087 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1639, d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7060 (p : Pattern) (ha : d1832 p = 1) (hb : d74857 p = 1) : d59737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1619 q = 1) : d1619 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1624 q = 1) (hb : d58747 q = 1) : d1797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1625 q = 1) (hb : d74856 q = 1) : d5076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d74856, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d74857 q = 1) : d5077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1626, d74857, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d74857 q = 1) : d5078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d74857 q = 1) : d5079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1831 q = 1) (hb : d74857 q = 1) : d1831 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1832 q = 1) (hb : d74857 q = 1) : d59737 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d59737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1832, d59737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7061 (p : Pattern) (ha : d67799 p = 1) (hb : d74857 p = 1) : d75543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1644 q = 1) : d1644 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1647 q = 1) (hb : d58747 q = 1) : d5091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1648 q = 1) (hb : d74856 q = 1) : d5092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d74856, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d74856, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1649 q = 1) (hb : d74857 q = 1) : d5093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d74857, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1649, d74857, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1650 q = 1) (hb : d74857 q = 1) : d5094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1653 q = 1) : d1653 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1657 q = 1) (hb : d58747 q = 1) : d5095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1658 q = 1) (hb : d74856 q = 1) : d5096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d74856, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d74856, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1659 q = 1) (hb : d74857 q = 1) : d5097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d74857, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1659, d74857, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4525 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4525, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67796 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67796, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67796, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67797 q = 1) (hb : d74857 q = 1) : d75541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67797, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67797, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67798 q = 1) (hb : d74857 q = 1) : d75542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67798, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67798, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67799 q = 1) (hb : d74857 q = 1) : d75543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67799, d75543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67799, d75543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7062 (p : Pattern) (ha : d67803 p = 1) (hb : d74857 p = 1) : d75546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1644 q = 1) : d1644 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1647 q = 1) (hb : d58747 q = 1) : d5091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1648 q = 1) (hb : d74856 q = 1) : d5092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d74856, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d74856, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1649 q = 1) (hb : d74857 q = 1) : d5093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d74857, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1649, d74857, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1650 q = 1) (hb : d74857 q = 1) : d5094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1653 q = 1) : d1653 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1657 q = 1) (hb : d58747 q = 1) : d5095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1658 q = 1) (hb : d74856 q = 1) : d5096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d74856, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d74856, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1659 q = 1) (hb : d74857 q = 1) : d5097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d74857, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1659, d74857, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4525 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4525, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67796 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67796, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67796, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67797 q = 1) (hb : d74857 q = 1) : d75541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67797, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67797, d75541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67798 q = 1) (hb : d74857 q = 1) : d75542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67798, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67798, d75542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d1803 q = 1) : d1803 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d1804 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d1805 q = 1) (hb : d58747 q = 1) : d5105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d58747, d5105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d1805, d58747, d5105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d1806 q = 1) (hb : d74856 q = 1) : d5106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d74856, d5106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1806, d74856, d5106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1807 q = 1) (hb : d74857 q = 1) : d5107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d74857, d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d1807, d74857, d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d1808 q = 1) (hb : d74857 q = 1) : d5108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d1809 q = 1) : d1809 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d1810 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d1811 q = 1) (hb : d58747 q = 1) : d5109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d58747, d5109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d1811, d58747, d5109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d1812 q = 1) (hb : d74856 q = 1) : d5110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d74856, d5110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, d74856, d5110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d1813 q = 1) (hb : d74857 q = 1) : d5111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d74857, d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d1813, d74857, d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4530 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4530, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67800 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67800, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67800, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67801 q = 1) (hb : d74857 q = 1) : d75544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67801, d75544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67801, d75544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67802 q = 1) (hb : d74857 q = 1) : d75545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67802, d75545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67802, d75545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67803 q = 1) (hb : d74857 q = 1) : d75546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67803, d75546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67803, d75546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7063 (p : Pattern) (ha : d67810 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4530, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67800 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67800, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67800, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67808 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67809 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67810 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7064 (p : Pattern) (ha : d67819 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4545, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67816 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67816, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67816, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67817 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67818 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67819 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7065 (p : Pattern) (ha : d67825 p = 1) (hb : d74857 p = 1) : d75552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d74857 q = 1) : d5081 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7058 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d74857 q = 1) : d5082 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d74857 q = 1) : d5088 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7058 q ha hb
    | true =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7059 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d74857 q = 1) : d5089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d74857 q = 1) : d5090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67804 q = 1) (hb : d74857 q = 1) : d75547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67804, d75547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7061 q ha hb
    | true =>
      simp only [d67804, d75547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7062 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d74857 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1839 q = 1) (hb : d74857 q = 1) : d59738 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d59738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7060 q ha hb
    | true =>
      simp only [d1839, d59738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67805 q = 1) (hb : d74857 q = 1) : d75548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67805, d75548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67805, d75548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67806 q = 1) (hb : d74857 q = 1) : d75549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67806, d75549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67806, d75549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67807 q = 1) (hb : d74857 q = 1) : d75550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67807, d75550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67807, d75550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67811 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7063 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d74857 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67812 q = 1) (hb : d74857 q = 1) : d59742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67812, d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67812, d59742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67813 q = 1) (hb : d74857 q = 1) : d59743 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67813, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67813, d59743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67814 q = 1) (hb : d74857 q = 1) : d59744 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67814, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67814, d59744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67815 q = 1) (hb : d74857 q = 1) : d75551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67815, d75551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67815, d75551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67820 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7064 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d74857 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67821 q = 1) (hb : d74857 q = 1) : d59746 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67821, d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67821, d59746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67822 q = 1) (hb : d74857 q = 1) : d59747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67822, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67822, d59747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67823 q = 1) (hb : d74857 q = 1) : d59748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67823, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67823, d59748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67824 q = 1) (hb : d74857 q = 1) : d59749 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67824, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67824, d59749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67825 q = 1) (hb : d74857 q = 1) : d75552 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67825, d75552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67825, d75552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7066 (p : Pattern) (ha : d67831 p = 1) (hb : d74857 p = 1) : d75558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67826 q = 1) (hb : d74857 q = 1) : d75553 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67826, d75553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67826, d75553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7065 q ha hb
  have h2 (q : Pattern) (ha : d67827 q = 1) (hb : d74857 q = 1) : d75554 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67827, d75554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67827, d75554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67828 q = 1) (hb : d74857 q = 1) : d75555 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67828, d75555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67828, d75555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67829 q = 1) (hb : d74857 q = 1) : d75556 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67829, d75556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67829, d75556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67830 q = 1) (hb : d74857 q = 1) : d75557 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67830, d75557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67830, d75557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67831 q = 1) (hb : d74857 q = 1) : d75558 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67831, d75558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67831, d75558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7067 (p : Pattern) (ha : d2112 p = 1) (hb : d74857 p = 1) : d5197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2102 q = 1) : d2102 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2107 q = 1) (hb : d58747 q = 1) : d2275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2108 q = 1) (hb : d74856 q = 1) : d5193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d74857 q = 1) : d5194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d74857 q = 1) : d5195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d74857 q = 1) : d5196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2112 q = 1) (hb : d74857 q = 1) : d5197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7068 (p : Pattern) (ha : d2122 p = 1) (hb : d74857 p = 1) : d5204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2102 q = 1) : d2102 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2107 q = 1) (hb : d58747 q = 1) : d2275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2108 q = 1) (hb : d74856 q = 1) : d5193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d74857 q = 1) : d5194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d74857 q = 1) : d5195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d74857 q = 1) : d5196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d2115 q = 1) : d2115 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2116 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2117 q = 1) (hb : d58747 q = 1) : d2298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d2118 q = 1) (hb : d74856 q = 1) : d5200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d74856, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d74856, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2119 q = 1) (hb : d74857 q = 1) : d5201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d74857, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2119, d74857, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d2120 q = 1) (hb : d74857 q = 1) : d5202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2121 q = 1) (hb : d74857 q = 1) : d5203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2122 q = 1) (hb : d74857 q = 1) : d5204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2122, d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro7069 (p : Pattern) (ha : d2310 p = 1) (hb : d74857 p = 1) : d59761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2102 q = 1) : d2102 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2107 q = 1) (hb : d58747 q = 1) : d2275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2108 q = 1) (hb : d74856 q = 1) : d5193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d74856, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d74857 q = 1) : d5194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2109, d74857, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d74857 q = 1) : d5195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d74857 q = 1) : d5196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2309 q = 1) (hb : d74857 q = 1) : d2309 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2310 q = 1) (hb : d74857 q = 1) : d59761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, d59761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2310, d59761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7070 (p : Pattern) (ha : d67839 p = 1) (hb : d74857 p = 1) : d75565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2127 q = 1) : d2127 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2130 q = 1) (hb : d58747 q = 1) : d5208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2131 q = 1) (hb : d74856 q = 1) : d5209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d74856, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d74856, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2132 q = 1) (hb : d74857 q = 1) : d5210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d74857, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2132, d74857, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2133 q = 1) (hb : d74857 q = 1) : d5211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d2136 q = 1) : d2136 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2140 q = 1) (hb : d58747 q = 1) : d5212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d2141 q = 1) (hb : d74856 q = 1) : d5213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d74856, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d74856, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2142 q = 1) (hb : d74857 q = 1) : d5214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d74857, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2142, d74857, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4566 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4566, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67836 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67836, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67836, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67837 q = 1) (hb : d74857 q = 1) : d75563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67837, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67837, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67838 q = 1) (hb : d74857 q = 1) : d75564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67838, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67838, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d67839 q = 1) (hb : d74857 q = 1) : d75565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67839, d75565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67839, d75565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7071 (p : Pattern) (ha : d67843 p = 1) (hb : d74857 p = 1) : d75568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2127 q = 1) : d2127 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2130 q = 1) (hb : d58747 q = 1) : d5208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2131 q = 1) (hb : d74856 q = 1) : d5209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d74856, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d74856, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2132 q = 1) (hb : d74857 q = 1) : d5210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d74857, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2132, d74857, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2133 q = 1) (hb : d74857 q = 1) : d5211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d2136 q = 1) : d2136 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2140 q = 1) (hb : d58747 q = 1) : d5212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d2141 q = 1) (hb : d74856 q = 1) : d5213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d74856, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d74856, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2142 q = 1) (hb : d74857 q = 1) : d5214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d74857, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2142, d74857, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4566 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d4566, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67836 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67836, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67836, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d67837 q = 1) (hb : d74857 q = 1) : d75563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67837, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67837, d75563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67838 q = 1) (hb : d74857 q = 1) : d75564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67838, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67838, d75564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1 q = 1) (hb : d2281 q = 1) : d2281 q = 1 := by
    exact hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d2282 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d2283 q = 1) (hb : d58747 q = 1) : d5222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d58747, d5222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d2283, d58747, d5222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d2284 q = 1) (hb : d74856 q = 1) : d5223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d74856, d5223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2284, d74856, d5223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d2285 q = 1) (hb : d74857 q = 1) : d5224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d74857, d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d2285, d74857, d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h24 (q : Pattern) (ha : d2286 q = 1) (hb : d74857 q = 1) : d5225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1 q = 1) (hb : d2287 q = 1) : d2287 q = 1 := by
    exact hb
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d2288 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d2289 q = 1) (hb : d58747 q = 1) : d5226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d58747, d5226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d2289, d58747, d5226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d2290 q = 1) (hb : d74856 q = 1) : d5227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d74856, d5227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, d74856, d5227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d2291 q = 1) (hb : d74857 q = 1) : d5228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d74857, d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d2291, d74857, d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d4571 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q hb ha
    | true =>
      simp only [d4571, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h32 (q : Pattern) (ha : d67840 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67840, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d67840, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h33 (q : Pattern) (ha : d67841 q = 1) (hb : d74857 q = 1) : d75566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67841, d75566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d67841, d75566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d67842 q = 1) (hb : d74857 q = 1) : d75567 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67842, d75567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d67842, d75567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d67843 q = 1) (hb : d74857 q = 1) : d75568 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67843, d75568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67843, d75568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro7072 (p : Pattern) (ha : d67850 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4571, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67840 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67840, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67840, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67848 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67849 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67850 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7073 (p : Pattern) (ha : d67859 p = 1) (hb : d74857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d74856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4586, d74856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67856 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67856, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67856, d74857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67857 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67858 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d67859 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro7074 (p : Pattern) (ha : d67865 p = 1) (hb : d74857 p = 1) : d75574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d74857 q = 1) : d5198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d5198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d5198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7067 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d74857 q = 1) : d5199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d5199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d5199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d74857 q = 1) : d5205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7067 q ha hb
    | true =>
      simp only [d2123, d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7068 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d74857 q = 1) : d5206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d74857 q = 1) : d5207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d5207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d5207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67844 q = 1) (hb : d74857 q = 1) : d75569 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67844, d75569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7070 q ha hb
    | true =>
      simp only [d67844, d75569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7071 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d74857 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2317 q = 1) (hb : d74857 q = 1) : d59762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d59762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7069 q ha hb
    | true =>
      simp only [d2317, d59762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67845 q = 1) (hb : d74857 q = 1) : d75570 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67845, d75570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67845, d75570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67846 q = 1) (hb : d74857 q = 1) : d75571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67846, d75571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67846, d75571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67847 q = 1) (hb : d74857 q = 1) : d75572 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67847, d75572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67847, d75572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67851 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7072 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d74857 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d67852 q = 1) (hb : d74857 q = 1) : d59766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67852, d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67852, d59766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67853 q = 1) (hb : d74857 q = 1) : d59767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67853, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d67853, d59767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d67854 q = 1) (hb : d74857 q = 1) : d59768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67854, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67854, d59768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d67855 q = 1) (hb : d74857 q = 1) : d75573 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67855, d75573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67855, d75573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d67860 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7073 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d74857 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67861 q = 1) (hb : d74857 q = 1) : d59770 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67861, d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d67861, d59770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d67862 q = 1) (hb : d74857 q = 1) : d59771 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67862, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67862, d59771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67863 q = 1) (hb : d74857 q = 1) : d59772 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67863, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d67863, d59772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d67864 q = 1) (hb : d74857 q = 1) : d59773 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67864, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d67864, d59773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d67865 q = 1) (hb : d74857 q = 1) : d75574 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d67865, d75574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d67865, d75574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro7075 (p : Pattern) (ha : d67871 p = 1) (hb : d74857 p = 1) : d75580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67866 q = 1) (hb : d74857 q = 1) : d75575 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d67866, d75575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67866, d75575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7074 q ha hb
  have h2 (q : Pattern) (ha : d67867 q = 1) (hb : d74857 q = 1) : d75576 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d67867, d75576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67867, d75576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d67868 q = 1) (hb : d74857 q = 1) : d75577 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d67868, d75577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67868, d75577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67869 q = 1) (hb : d74857 q = 1) : d75578 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d67869, d75578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67869, d75578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67870 q = 1) (hb : d74857 q = 1) : d75579 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d67870, d75579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67870, d75579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67871 q = 1) (hb : d74857 q = 1) : d75580 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d67871, d75580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67871, d75580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7076 (p : Pattern) (ha : d67877 p = 1) (hb : d74857 p = 1) : d75586 p = 1 := by
  have h0 (q : Pattern) (ha : d67718 q = 1) (hb : d74857 q = 1) : d75499 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67718, d75499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7030 q ha hb
    | true =>
      simp only [d67718, d75499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7039 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67755 q = 1) (hb : d74857 q = 1) : d75518 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67755, d75518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67755, d75518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7048 q ha hb
  have h3 (q : Pattern) (ha : d67756 q = 1) (hb : d74857 q = 1) : d75519 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67756, d75519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67756, d75519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d67793 q = 1) (hb : d74857 q = 1) : d75538 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67793, d75538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67793, d75538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7057 q ha hb
  have h5 (q : Pattern) (ha : d67794 q = 1) (hb : d74857 q = 1) : d75539 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67794, d75539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67794, d75539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67795 q = 1) (hb : d74857 q = 1) : d75540 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67795, d75540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67795, d75540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67832 q = 1) (hb : d74857 q = 1) : d75559 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67832, d75559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67832, d75559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7066 q ha hb
  have h8 (q : Pattern) (ha : d67833 q = 1) (hb : d74857 q = 1) : d75560 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67833, d75560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67833, d75560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d67834 q = 1) (hb : d74857 q = 1) : d75561 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67834, d75561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67834, d75561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67835 q = 1) (hb : d74857 q = 1) : d75562 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67835, d75562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67835, d75562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67872 q = 1) (hb : d74857 q = 1) : d75581 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d67872, d75581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67872, d75581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7075 q ha hb
  have h12 (q : Pattern) (ha : d67873 q = 1) (hb : d74857 q = 1) : d75582 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d67873, d75582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67873, d75582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d67874 q = 1) (hb : d74857 q = 1) : d75583 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d67874, d75583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67874, d75583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d67875 q = 1) (hb : d74857 q = 1) : d75584 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d67875, d75584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67875, d75584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d67876 q = 1) (hb : d74857 q = 1) : d75585 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d67876, d75585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67876, d75585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d67877 q = 1) (hb : d74857 q = 1) : d75586 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d67877, d75586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d67877, d75586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7077 (p : Pattern) (ha : d67883 p = 1) (hb : d74857 p = 1) : d75592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67878 q = 1) (hb : d74857 q = 1) : d75587 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d67878, d75587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7076 q ha hb
    | true =>
      simp only [d67878, d75587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67879 q = 1) (hb : d74857 q = 1) : d75588 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d67879, d75588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67879, d75588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67880 q = 1) (hb : d74857 q = 1) : d75589 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d67880, d75589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67880, d75589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67881 q = 1) (hb : d74857 q = 1) : d75590 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d67881, d75590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67881, d75590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67882 q = 1) (hb : d74857 q = 1) : d75591 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d67882, d75591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67882, d75591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67883 q = 1) (hb : d74857 q = 1) : d75592 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d67883, d75592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67883, d75592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7078 (p : Pattern) (ha : d67889 p = 1) (hb : d74857 p = 1) : d75598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67884 q = 1) (hb : d74857 q = 1) : d75593 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d67884, d75593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7077 q ha hb
    | true =>
      simp only [d67884, d75593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67885 q = 1) (hb : d74857 q = 1) : d75594 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d67885, d75594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67885, d75594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67886 q = 1) (hb : d74857 q = 1) : d75595 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d67886, d75595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67886, d75595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67887 q = 1) (hb : d74857 q = 1) : d75596 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d67887, d75596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67887, d75596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67888 q = 1) (hb : d74857 q = 1) : d75597 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d67888, d75597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67888, d75597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67889 q = 1) (hb : d74857 q = 1) : d75598 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d67889, d75598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67889, d75598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7079 (p : Pattern) (ha : d67895 p = 1) (hb : d74857 p = 1) : d75604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67890 q = 1) (hb : d74857 q = 1) : d75599 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d67890, d75599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7078 q ha hb
    | true =>
      simp only [d67890, d75599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67891 q = 1) (hb : d74857 q = 1) : d75600 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d67891, d75600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67891, d75600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67892 q = 1) (hb : d74857 q = 1) : d75601 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d67892, d75601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67892, d75601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67893 q = 1) (hb : d74857 q = 1) : d75602 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d67893, d75602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67893, d75602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67894 q = 1) (hb : d74857 q = 1) : d75603 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d67894, d75603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67894, d75603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67895 q = 1) (hb : d74857 q = 1) : d75604 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d67895, d75604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67895, d75604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7080 (p : Pattern) (ha : d67901 p = 1) (hb : d74857 p = 1) : d75610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67896 q = 1) (hb : d74857 q = 1) : d75605 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d67896, d75605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7079 q ha hb
    | true =>
      simp only [d67896, d75605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67897 q = 1) (hb : d74857 q = 1) : d75606 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d67897, d75606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67897, d75606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67898 q = 1) (hb : d74857 q = 1) : d75607 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d67898, d75607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67898, d75607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67899 q = 1) (hb : d74857 q = 1) : d75608 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d67899, d75608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67899, d75608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67900 q = 1) (hb : d74857 q = 1) : d75609 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d67900, d75609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67900, d75609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67901 q = 1) (hb : d74857 q = 1) : d75610 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d67901, d75610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67901, d75610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7081 (p : Pattern) (ha : d67907 p = 1) (hb : d74857 p = 1) : d75616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67902 q = 1) (hb : d74857 q = 1) : d75611 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d67902, d75611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7080 q ha hb
    | true =>
      simp only [d67902, d75611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67903 q = 1) (hb : d74857 q = 1) : d75612 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d67903, d75612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67903, d75612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67904 q = 1) (hb : d74857 q = 1) : d75613 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d67904, d75613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67904, d75613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67905 q = 1) (hb : d74857 q = 1) : d75614 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67905, d75614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67905, d75614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67906 q = 1) (hb : d74857 q = 1) : d75615 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d67906, d75615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67906, d75615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67907 q = 1) (hb : d74857 q = 1) : d75616 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d67907, d75616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67907, d75616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7082 (p : Pattern) (ha : d67913 p = 1) (hb : d74857 p = 1) : d75622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67908 q = 1) (hb : d74857 q = 1) : d75617 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d67908, d75617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7081 q ha hb
    | true =>
      simp only [d67908, d75617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67909 q = 1) (hb : d74857 q = 1) : d75618 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d67909, d75618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67909, d75618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67910 q = 1) (hb : d74857 q = 1) : d75619 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67910, d75619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67910, d75619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67911 q = 1) (hb : d74857 q = 1) : d75620 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d67911, d75620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67911, d75620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67912 q = 1) (hb : d74857 q = 1) : d75621 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d67912, d75621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67912, d75621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67913 q = 1) (hb : d74857 q = 1) : d75622 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d67913, d75622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67913, d75622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7083 (p : Pattern) (ha : d67919 p = 1) (hb : d74857 p = 1) : d75628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67914 q = 1) (hb : d74857 q = 1) : d75623 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d67914, d75623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7082 q ha hb
    | true =>
      simp only [d67914, d75623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d67915 q = 1) (hb : d74857 q = 1) : d75624 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d67915, d75624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67915, d75624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67916 q = 1) (hb : d74857 q = 1) : d75625 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d67916, d75625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67916, d75625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d67917 q = 1) (hb : d74857 q = 1) : d75626 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d67917, d75626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67917, d75626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d67918 q = 1) (hb : d74857 q = 1) : d75627 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d67918, d75627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d67918, d75627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d67919 q = 1) (hb : d74857 q = 1) : d75628 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d67919, d75628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67919, d75628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7084 (p : Pattern) (ha : d75447 p = 1) (hb : d75628 p = 1) : d75628 p = 1 := by
  have h0 (q : Pattern) (ha : d75447 q = 1) (hb : d75628 q = 1) : d75628 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro7085 (p : Pattern) (ha : d53655 p = 1) (hb : d74857 p = 1) : d69762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d287 q = 1) (hb : d74856 q = 1) : d4696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d74856, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d74856, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d288 q = 1) (hb : d74857 q = 1) : d4697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d74857, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d288, d74857, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d289 q = 1) (hb : d74857 q = 1) : d4698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d290 q = 1) (hb : d74857 q = 1) : d4699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53655 q = 1) (hb : d74857 q = 1) : d69762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d69762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d69762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7086 (p : Pattern) (ha : d53665 p = 1) (hb : d74857 p = 1) : d69772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d243 q = 1) : d243 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d244 q = 1) (hb : d58747 q = 1) : d451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53661 q = 1) (hb : d74856 q = 1) : d69768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d74856, d69768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53661, d74856, d69768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53662 q = 1) (hb : d74857 q = 1) : d69769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d74857, d69769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53662, d74857, d69769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53663 q = 1) (hb : d74857 q = 1) : d69770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d69770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d69770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53664 q = 1) (hb : d74857 q = 1) : d69771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d69771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d69771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53665 q = 1) (hb : d74857 q = 1) : d69772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d69772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d69772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7087 (p : Pattern) (ha : d53671 p = 1) (hb : d74857 p = 1) : d69778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d74857 q = 1) : d4701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7022 q ha hb
    | true =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7023 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d74857 q = 1) : d4702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d74857 q = 1) : d69760 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d69760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d69760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d74857 q = 1) : d69761 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d69761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d69761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d74857 q = 1) : d69763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d69763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d69763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7085 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d74857 q = 1) : d69764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d69764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d69764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d74857 q = 1) : d69765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d69765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d69765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d74857 q = 1) : d69766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d69766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d69766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d74857 q = 1) : d69767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d69767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d69767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d74857 q = 1) : d69773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d69773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d69773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7086 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d74857 q = 1) : d69774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d69774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d69774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d74857 q = 1) : d69775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d69775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d69775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d74857 q = 1) : d69776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d69776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d69776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d74857 q = 1) : d69777 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d69777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d69777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d74857 q = 1) : d69778 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d69778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d69778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7088 (p : Pattern) (ha : d53677 p = 1) (hb : d74857 p = 1) : d69784 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d74857 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53672 q = 1) (hb : d74857 q = 1) : d69779 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d69779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53672, d69779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7087 q ha hb
  have h3 (q : Pattern) (ha : d53673 q = 1) (hb : d74857 q = 1) : d69780 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d69780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53673, d69780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53674 q = 1) (hb : d74857 q = 1) : d69781 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d69781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53674, d69781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53675 q = 1) (hb : d74857 q = 1) : d69782 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d69782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53675, d69782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53676 q = 1) (hb : d74857 q = 1) : d69783 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d69783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53676, d69783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53677 q = 1) (hb : d74857 q = 1) : d69784 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d69784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53677, d69784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7089 (p : Pattern) (ha : d53680 p = 1) (hb : d74857 p = 1) : d69787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d500 q = 1) : d500 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d501 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d502 q = 1) (hb : d58747 q = 1) : d626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d503 q = 1) (hb : d74856 q = 1) : d4781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d74856, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d74856, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d504 q = 1) (hb : d74857 q = 1) : d4782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d74857, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d504, d74857, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d505 q = 1) (hb : d74857 q = 1) : d4783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d506 q = 1) (hb : d74857 q = 1) : d4784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53680 q = 1) (hb : d74857 q = 1) : d69787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d69787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d69787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7090 (p : Pattern) (ha : d53691 p = 1) (hb : d74857 p = 1) : d69797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d689 q = 1) : d689 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d730 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53686 q = 1) (hb : d58747 q = 1) : d720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d58747, d720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53686, d58747, d720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53687 q = 1) (hb : d74856 q = 1) : d69793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d74856, d69793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53687, d74856, d69793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53688 q = 1) (hb : d74857 q = 1) : d69794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d74857, d69794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53688, d74857, d69794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53689 q = 1) (hb : d74857 q = 1) : d69795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d69795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d69795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53690 q = 1) (hb : d74857 q = 1) : d69796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d69796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d69796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53691 q = 1) (hb : d74857 q = 1) : d69797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d69797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d69797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7091 (p : Pattern) (ha : d53697 p = 1) (hb : d74857 p = 1) : d69803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d74857 q = 1) : d4786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7031 q ha hb
    | true =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7032 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d74857 q = 1) : d4787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d74857 q = 1) : d69785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d69785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d69785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d74857 q = 1) : d69786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d69786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d69786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d74857 q = 1) : d69788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d69788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d69788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7089 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d74857 q = 1) : d69789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d69789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d69789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d74857 q = 1) : d69790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d69790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d69790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d74857 q = 1) : d69791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d69791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d69791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d74857 q = 1) : d69792 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d69792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d69792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d74857 q = 1) : d69798 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d69798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d69798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7090 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d74857 q = 1) : d69799 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d69799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d69799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d74857 q = 1) : d69800 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d69800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d69800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d74857 q = 1) : d69801 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d69801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d69801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d74857 q = 1) : d69802 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d69802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d69802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d74857 q = 1) : d69803 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d69803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d69803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7092 (p : Pattern) (ha : d53703 p = 1) (hb : d74857 p = 1) : d69809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d74857 q = 1) : d69804 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d69804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d69804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7091 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d74857 q = 1) : d69805 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d69805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d69805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d74857 q = 1) : d69806 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d69806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d69806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d74857 q = 1) : d69807 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d69807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d69807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d74857 q = 1) : d69808 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d69808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d69808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d74857 q = 1) : d69809 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d69809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d69809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7093 (p : Pattern) (ha : d53707 p = 1) (hb : d74857 p = 1) : d69813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d792 q = 1) : d792 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d793 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d794 q = 1) (hb : d58747 q = 1) : d932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d795 q = 1) (hb : d74856 q = 1) : d4876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d74856, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d74856, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d796 q = 1) (hb : d74857 q = 1) : d4877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d74857, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d796, d74857, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d797 q = 1) (hb : d74857 q = 1) : d4878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d798 q = 1) (hb : d74857 q = 1) : d4879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53707 q = 1) (hb : d74857 q = 1) : d69813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d69813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d69813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7094 (p : Pattern) (ha : d53718 p = 1) (hb : d74857 p = 1) : d69823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1011 q = 1) : d1011 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1063 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53713 q = 1) (hb : d58747 q = 1) : d1053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d58747, d1053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53713, d58747, d1053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53714 q = 1) (hb : d74856 q = 1) : d69819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d74856, d69819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53714, d74856, d69819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53715 q = 1) (hb : d74857 q = 1) : d69820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d74857, d69820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53715, d74857, d69820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53716 q = 1) (hb : d74857 q = 1) : d69821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d69821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d69821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53717 q = 1) (hb : d74857 q = 1) : d69822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d69822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d69822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53718 q = 1) (hb : d74857 q = 1) : d69823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d69823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d69823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7095 (p : Pattern) (ha : d53724 p = 1) (hb : d74857 p = 1) : d69829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d74857 q = 1) : d4881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7040 q ha hb
    | true =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7041 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d74857 q = 1) : d4882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d74857 q = 1) : d69811 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d69811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d69811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d74857 q = 1) : d69812 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d69812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d69812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d74857 q = 1) : d69814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d69814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d69814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7093 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d74857 q = 1) : d69815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d69815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d69815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d74857 q = 1) : d69816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d69816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d69816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d74857 q = 1) : d69817 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d69817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d69817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d74857 q = 1) : d69818 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d69818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d69818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d74857 q = 1) : d69824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d69824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d69824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7094 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d74857 q = 1) : d69825 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d69825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d69825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d74857 q = 1) : d69826 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d69826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d69826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d74857 q = 1) : d69827 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d69827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d69827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d74857 q = 1) : d69828 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d69828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d69828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d74857 q = 1) : d69829 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d69829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d69829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7096 (p : Pattern) (ha : d53730 p = 1) (hb : d74857 p = 1) : d69835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d74857 q = 1) : d69830 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d69830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d69830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7095 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d74857 q = 1) : d69831 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d69831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d69831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d74857 q = 1) : d69832 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d69832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d69832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d74857 q = 1) : d69833 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d69833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d69833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d74857 q = 1) : d69834 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d69834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d69834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d74857 q = 1) : d69835 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d69835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d69835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7097 (p : Pattern) (ha : d53735 p = 1) (hb : d74857 p = 1) : d69840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1171 q = 1) : d1171 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1172 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1173 q = 1) (hb : d58747 q = 1) : d1343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1174 q = 1) (hb : d74856 q = 1) : d4972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d74856, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d74856, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1175 q = 1) (hb : d74857 q = 1) : d4973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d74857, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1175, d74857, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1176 q = 1) (hb : d74857 q = 1) : d4974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1177 q = 1) (hb : d74857 q = 1) : d4975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53735 q = 1) (hb : d74857 q = 1) : d69840 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d69840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d69840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7098 (p : Pattern) (ha : d53746 p = 1) (hb : d74857 p = 1) : d69850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1436 q = 1) : d1436 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1497 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53741 q = 1) (hb : d58747 q = 1) : d1487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d58747, d1487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53741, d58747, d1487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53742 q = 1) (hb : d74856 q = 1) : d69846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d74856, d69846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53742, d74856, d69846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53743 q = 1) (hb : d74857 q = 1) : d69847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d74857, d69847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53743, d74857, d69847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53744 q = 1) (hb : d74857 q = 1) : d69848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d69848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d69848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53745 q = 1) (hb : d74857 q = 1) : d69849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d69849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d69849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53746 q = 1) (hb : d74857 q = 1) : d69850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d69850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d69850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7099 (p : Pattern) (ha : d53752 p = 1) (hb : d74857 p = 1) : d69856 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d74857 q = 1) : d4977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7049 q ha hb
    | true =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7050 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d74857 q = 1) : d4978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d74857 q = 1) : d69838 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d69838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d69838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d74857 q = 1) : d69839 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d69839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d69839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d74857 q = 1) : d69841 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d69841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d69841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7097 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d74857 q = 1) : d69842 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d69842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d69842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d74857 q = 1) : d69843 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d69843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d69843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d74857 q = 1) : d69844 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d69844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d69844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d74857 q = 1) : d69845 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d69845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d69845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d74857 q = 1) : d69851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d69851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d69851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7098 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d74857 q = 1) : d69852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d69852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d69852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d74857 q = 1) : d69853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d69853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d69853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d74857 q = 1) : d69854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d69854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d69854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d74857 q = 1) : d69855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d69855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d69855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d74857 q = 1) : d69856 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d69856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d69856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7100 (p : Pattern) (ha : d53758 p = 1) (hb : d74857 p = 1) : d69862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d74857 q = 1) : d69857 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d69857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d69857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7099 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d74857 q = 1) : d69858 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d69858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d69858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d74857 q = 1) : d69859 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d69859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d69859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d74857 q = 1) : d69860 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d69860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d69860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d74857 q = 1) : d69861 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d69861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d69861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d74857 q = 1) : d69862 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d69862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d69862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7101 (p : Pattern) (ha : d53764 p = 1) (hb : d74857 p = 1) : d69868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1632 q = 1) : d1632 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1633 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1634 q = 1) (hb : d58747 q = 1) : d1820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1635 q = 1) (hb : d74856 q = 1) : d5083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d74856, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d74856, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1636 q = 1) (hb : d74857 q = 1) : d5084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d74857, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1636, d74857, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1637 q = 1) (hb : d74857 q = 1) : d5085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1638 q = 1) (hb : d74857 q = 1) : d5086 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53764 q = 1) (hb : d74857 q = 1) : d69868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d69868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d69868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7102 (p : Pattern) (ha : d53775 p = 1) (hb : d74857 p = 1) : d69878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d1913 q = 1) : d1913 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1974 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53770 q = 1) (hb : d58747 q = 1) : d1964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d58747, d1964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53770, d58747, d1964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53771 q = 1) (hb : d74856 q = 1) : d69874 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d74856, d69874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53771, d74856, d69874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53772 q = 1) (hb : d74857 q = 1) : d69875 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d74857, d69875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53772, d74857, d69875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53773 q = 1) (hb : d74857 q = 1) : d69876 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d69876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d69876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53774 q = 1) (hb : d74857 q = 1) : d69877 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d69877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d69877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53775 q = 1) (hb : d74857 q = 1) : d69878 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d69878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d69878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7103 (p : Pattern) (ha : d53781 p = 1) (hb : d74857 p = 1) : d69884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d74857 q = 1) : d5088 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7058 q ha hb
    | true =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7059 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d74857 q = 1) : d5089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d74857 q = 1) : d69866 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d69866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d69866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d74857 q = 1) : d69867 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d69867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d69867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d74857 q = 1) : d69869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d69869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d69869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7101 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d74857 q = 1) : d69870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d69870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d69870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d74857 q = 1) : d69871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d69871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d69871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d74857 q = 1) : d69872 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d69872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d69872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d74857 q = 1) : d69873 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d69873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d69873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d74857 q = 1) : d69879 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d69879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d69879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7102 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d74857 q = 1) : d69880 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d69880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d69880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d74857 q = 1) : d69881 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d69881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d69881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d74857 q = 1) : d69882 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d69882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d69882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d74857 q = 1) : d69883 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d69883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d69883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d74857 q = 1) : d69884 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d69884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d69884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7104 (p : Pattern) (ha : d53787 p = 1) (hb : d74857 p = 1) : d69890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d74857 q = 1) : d69885 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d69885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d69885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7103 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d74857 q = 1) : d69886 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d69886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d69886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d74857 q = 1) : d69887 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d69887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d69887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d74857 q = 1) : d69888 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d69888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d69888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d74857 q = 1) : d69889 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d69889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d69889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d74857 q = 1) : d69890 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d69890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d69890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7105 (p : Pattern) (ha : d53794 p = 1) (hb : d74857 p = 1) : d69897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2115 q = 1) : d2115 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2116 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2117 q = 1) (hb : d58747 q = 1) : d2298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2118 q = 1) (hb : d74856 q = 1) : d5200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d74856, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d74856, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2119 q = 1) (hb : d74857 q = 1) : d5201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d74857, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2119, d74857, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2120 q = 1) (hb : d74857 q = 1) : d5202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2121 q = 1) (hb : d74857 q = 1) : d5203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53794 q = 1) (hb : d74857 q = 1) : d69897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d69897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d69897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7106 (p : Pattern) (ha : d53805 p = 1) (hb : d74857 p = 1) : d69907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d2391 q = 1) : d2391 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2452 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53800 q = 1) (hb : d58747 q = 1) : d2442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d58747, d2442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53800, d58747, d2442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d53801 q = 1) (hb : d74856 q = 1) : d69903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d74856, d69903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53801, d74856, d69903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53802 q = 1) (hb : d74857 q = 1) : d69904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d74857, d69904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53802, d74857, d69904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d53803 q = 1) (hb : d74857 q = 1) : d69905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d69905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d69905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53804 q = 1) (hb : d74857 q = 1) : d69906 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d69906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d69906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53805 q = 1) (hb : d74857 q = 1) : d69907 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d69907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d69907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro7107 (p : Pattern) (ha : d53811 p = 1) (hb : d74857 p = 1) : d69913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d74857 q = 1) : d5205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7067 q ha hb
    | true =>
      simp only [d2123, d5205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7068 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d74857 q = 1) : d5206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d5206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d74857 q = 1) : d69895 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d69895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d69895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d74857 q = 1) : d69896 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d69896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d69896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d74857 q = 1) : d69898 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d69898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d69898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7105 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d74857 q = 1) : d69899 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d69899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d69899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d74857 q = 1) : d69900 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d69900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d69900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d74857 q = 1) : d69901 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d69901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d69901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d74857 q = 1) : d69902 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d69902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d69902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d74857 q = 1) : d69908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d69908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d69908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7106 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d74857 q = 1) : d69909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d69909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d69909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d74857 q = 1) : d69910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d69910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d69910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d74857 q = 1) : d69911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d69911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d69911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d74857 q = 1) : d69912 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d69912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d69912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d74857 q = 1) : d69913 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d69913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d69913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7108 (p : Pattern) (ha : d53817 p = 1) (hb : d74857 p = 1) : d69919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d74857 q = 1) : d69914 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d69914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d69914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7107 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d74857 q = 1) : d69915 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d69915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d69915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d74857 q = 1) : d69916 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d69916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d69916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d74857 q = 1) : d69917 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d69917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d69917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d74857 q = 1) : d69918 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d69918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d69918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d74857 q = 1) : d69919 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d69919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d69919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7109 (p : Pattern) (ha : d53823 p = 1) (hb : d74857 p = 1) : d69925 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d74857 q = 1) : d69810 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d69810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7088 q ha hb
    | true =>
      simp only [d53704, d69810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7092 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d74857 q = 1) : d69836 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d69836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d69836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7096 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d74857 q = 1) : d69837 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d69837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d69837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d74857 q = 1) : d69863 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d69863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d69863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7100 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d74857 q = 1) : d69864 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d69864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d69864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d74857 q = 1) : d69865 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d69865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d69865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d74857 q = 1) : d69891 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d69891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d69891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7104 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d74857 q = 1) : d69892 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d69892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d69892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d74857 q = 1) : d69893 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d69893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d69893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d74857 q = 1) : d69894 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d69894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d69894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d74857 q = 1) : d69920 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d69920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d69920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7108 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d74857 q = 1) : d69921 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d69921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d69921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d74857 q = 1) : d69922 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d69922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d69922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d74857 q = 1) : d69923 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d69923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d69923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d74857 q = 1) : d69924 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d69924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d69924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d74857 q = 1) : d69925 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d69925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d69925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7110 (p : Pattern) (ha : d53829 p = 1) (hb : d74857 p = 1) : d69931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d74857 q = 1) : d69926 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d69926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7109 q ha hb
    | true =>
      simp only [d53824, d69926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d74857 q = 1) : d69927 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d69927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d69927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d74857 q = 1) : d69928 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d69928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d69928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d74857 q = 1) : d69929 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d69929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d69929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d74857 q = 1) : d69930 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d69930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d69930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d74857 q = 1) : d69931 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d69931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d69931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7111 (p : Pattern) (ha : d53835 p = 1) (hb : d74857 p = 1) : d69937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d74857 q = 1) : d69932 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d69932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7110 q ha hb
    | true =>
      simp only [d53830, d69932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d74857 q = 1) : d69933 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d69933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d69933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d74857 q = 1) : d69934 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d69934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d69934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d74857 q = 1) : d69935 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d69935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d69935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d74857 q = 1) : d69936 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d69936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d69936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d74857 q = 1) : d69937 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d69937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d69937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7112 (p : Pattern) (ha : d53841 p = 1) (hb : d74857 p = 1) : d69943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d74857 q = 1) : d69938 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d69938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7111 q ha hb
    | true =>
      simp only [d53836, d69938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d74857 q = 1) : d69939 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d69939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d69939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d74857 q = 1) : d69940 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d69940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d69940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d74857 q = 1) : d69941 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d69941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d69941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d74857 q = 1) : d69942 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d69942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d69942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d74857 q = 1) : d69943 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d69943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d69943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7113 (p : Pattern) (ha : d53847 p = 1) (hb : d74857 p = 1) : d69949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d74857 q = 1) : d69944 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d69944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7112 q ha hb
    | true =>
      simp only [d53842, d69944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d74857 q = 1) : d69945 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d69945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d69945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d74857 q = 1) : d69946 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d69946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d69946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d74857 q = 1) : d69947 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d69947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d69947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d74857 q = 1) : d69948 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d69948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d69948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d74857 q = 1) : d69949 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d69949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d69949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7114 (p : Pattern) (ha : d53853 p = 1) (hb : d74857 p = 1) : d69955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d74857 q = 1) : d69950 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d69950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7113 q ha hb
    | true =>
      simp only [d53848, d69950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d74857 q = 1) : d69951 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d69951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d69951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d74857 q = 1) : d69952 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d69952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d69952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d74857 q = 1) : d69953 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d69953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d69953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d74857 q = 1) : d69954 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d69954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, d69954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d74857 q = 1) : d69955 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d69955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, d69955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7115 (p : Pattern) (ha : d53859 p = 1) (hb : d74857 p = 1) : d69961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d74857 q = 1) : d69956 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d69956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7114 q ha hb
    | true =>
      simp only [d53854, d69956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d74857 q = 1) : d69957 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d69957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d69957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d74857 q = 1) : d69958 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d69958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d69958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d74857 q = 1) : d69959 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d69959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d69959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d74857 q = 1) : d69960 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d69960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d69960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d74857 q = 1) : d69961 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d69961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d69961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7116 (p : Pattern) (ha : d53865 p = 1) (hb : d74857 p = 1) : d69967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d74857 q = 1) : d69962 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d69962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7115 q ha hb
    | true =>
      simp only [d53860, d69962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d74857 q = 1) : d69963 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d69963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d69963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d74857 q = 1) : d69964 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d69964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d69964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d74857 q = 1) : d69965 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d69965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d69965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d74857 q = 1) : d69966 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d69966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d69966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d74857 q = 1) : d69967 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d69967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d69967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7117 (p : Pattern) (ha : d104 p = 1) (hb : d75156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d75153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d75153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d75153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d75154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d75154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d75154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d75155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d75155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d75155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d104 q = 1) (hb : d75156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d75156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d75156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7118 (p : Pattern) (ha : d111 p = 1) (hb : d75160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101 q = 1) (hb : d75153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d75153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d75153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102 q = 1) (hb : d75154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d75154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d75154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d103 q = 1) (hb : d75155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d75155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d75155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d50 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108 q = 1) (hb : d75157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d75157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108, d75157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d109 q = 1) (hb : d75158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d75158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d75158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d110 q = 1) (hb : d75159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d75159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d75159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d111 q = 1) (hb : d75160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d75160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d111, d75160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7119 (p : Pattern) (ha : d406 p = 1) (hb : d75165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d50 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108 q = 1) (hb : d75157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d75157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d75157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109 q = 1) (hb : d75158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d75158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d75158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d110 q = 1) (hb : d75159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d75159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d75159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d406 q = 1) (hb : d75165 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d75165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d75165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7120 (p : Pattern) (ha : d462 p = 1) (hb : d75174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d459 q = 1) (hb : d75171 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d75171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d75171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d460 q = 1) (hb : d75172 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d75172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d75172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d461 q = 1) (hb : d75173 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d75173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d75173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d462 q = 1) (hb : d75174 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d75174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d75174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7121 (p : Pattern) (ha : d53647 p = 1) (hb : d75180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d75161 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d75161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7117 q ha hb
    | true =>
      simp only [d112, d75161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7118 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d75162 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d75162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d75162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d75163 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d75163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, d75163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d75164 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d75164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d75164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d75166 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d75166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d75166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7119 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d75167 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d75167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, d75167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d75168 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d75168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, d75168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d75169 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d75169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, d75169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d75170 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d75170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, d75170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d75175 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d75175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d75175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7120 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d75176 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d75176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, d75176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d75177 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d75177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, d75177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d75178 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d75178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, d75178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d75179 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d75179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, d75179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d75180 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d75180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, d75180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7122 (p : Pattern) (ha : d4693 p = 1) (hb : d75189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d75186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, d75186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, d75186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d75187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, d75187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, d75187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d75188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, d75188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, d75188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4693 q = 1) (hb : d75189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4693, d75189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4693, d75189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7123 (p : Pattern) (ha : d4700 p = 1) (hb : d75193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d370 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4689 q = 1) (hb : d52007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4690 q = 1) (hb : d75186 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4690, d75186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4690, d75186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4691 q = 1) (hb : d75187 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4691, d75187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4691, d75187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4692 q = 1) (hb : d75188 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4692, d75188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4692, d75188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d390 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4696 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4697 q = 1) (hb : d75190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, d75190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4697, d75190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4698 q = 1) (hb : d75191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, d75191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, d75191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4699 q = 1) (hb : d75192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, d75192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, d75192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4700 q = 1) (hb : d75193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4700, d75193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4700, d75193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7124 (p : Pattern) (ha : d69762 p = 1) (hb : d75198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d390 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4696 q = 1) (hb : d52023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4697 q = 1) (hb : d75190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4697, d75190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4697, d75190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4698 q = 1) (hb : d75191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4698, d75191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4698, d75191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4699 q = 1) (hb : d75192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4699, d75192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4699, d75192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69762 q = 1) (hb : d75198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69762, d75198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69762, d75198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7125 (p : Pattern) (ha : d69772 p = 1) (hb : d75207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d451 q = 1) (hb : d52061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52061 q = 1) (hb : d69768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69769 q = 1) (hb : d75204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69769, d75204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69769, d75204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69770 q = 1) (hb : d75205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69770, d75205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69770, d75205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69771 q = 1) (hb : d75206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69771, d75206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69771, d75206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69772 q = 1) (hb : d75207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69772, d75207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69772, d75207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7126 (p : Pattern) (ha : d69778 p = 1) (hb : d75213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4701 q = 1) (hb : d75194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4701, d75194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7122 q ha hb
    | true =>
      simp only [d4701, d75194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7123 q ha hb
  have h2 (q : Pattern) (ha : d4702 q = 1) (hb : d75195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4702, d75195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4702, d75195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69760 q = 1) (hb : d75196 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69760, d75196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69760, d75196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69761 q = 1) (hb : d75197 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69761, d75197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69761, d75197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69763 q = 1) (hb : d75199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69763, d75199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69763, d75199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7124 q ha hb
  have h6 (q : Pattern) (ha : d69764 q = 1) (hb : d75200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69764, d75200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69764, d75200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69765 q = 1) (hb : d75201 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69765, d75201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69765, d75201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69766 q = 1) (hb : d75202 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69766, d75202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69766, d75202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69767 q = 1) (hb : d75203 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69767, d75203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69767, d75203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69773 q = 1) (hb : d75208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69773, d75208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69773, d75208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7125 q ha hb
  have h11 (q : Pattern) (ha : d69774 q = 1) (hb : d75209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69774, d75209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69774, d75209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69775 q = 1) (hb : d75210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69775, d75210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69775, d75210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69776 q = 1) (hb : d75211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69776, d75211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69776, d75211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69777 q = 1) (hb : d75212 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69777, d75212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69777, d75212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69778 q = 1) (hb : d75213 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69778, d75213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69778, d75213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7127 (p : Pattern) (ha : d69784 p = 1) (hb : d75219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d75181 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d75181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, d75181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7121 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d75182 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d75182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, d75182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d75183 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d75183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, d75183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d75184 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d75184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, d75184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d75185 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d75185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d75185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69779 q = 1) (hb : d75214 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69779, d75214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69779, d75214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7126 q ha hb
  have h7 (q : Pattern) (ha : d69780 q = 1) (hb : d75215 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69780, d75215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69780, d75215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69781 q = 1) (hb : d75216 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69781, d75216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69781, d75216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69782 q = 1) (hb : d75217 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69782, d75217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69782, d75217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69783 q = 1) (hb : d75218 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69783, d75218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69783, d75218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69784 q = 1) (hb : d75219 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69784, d75219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69784, d75219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7128 (p : Pattern) (ha : d4778 p = 1) (hb : d75223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d603 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d75220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, d75220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, d75220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d75221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, d75221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, d75221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d75222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, d75222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, d75222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4778 q = 1) (hb : d75223 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4778, d75223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4778, d75223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7129 (p : Pattern) (ha : d4785 p = 1) (hb : d75227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d603 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4774 q = 1) (hb : d52234 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4775 q = 1) (hb : d75220 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4775, d75220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4775, d75220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4776 q = 1) (hb : d75221 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4776, d75221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4776, d75221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4777 q = 1) (hb : d75222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4777, d75222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4777, d75222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d626 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4781 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4782 q = 1) (hb : d75224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, d75224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4782, d75224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4783 q = 1) (hb : d75225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, d75225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, d75225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4784 q = 1) (hb : d75226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, d75226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, d75226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4785 q = 1) (hb : d75227 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4785, d75227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4785, d75227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7130 (p : Pattern) (ha : d69787 p = 1) (hb : d75232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d626 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4781 q = 1) (hb : d52247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4782 q = 1) (hb : d75224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4782, d75224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4782, d75224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4783 q = 1) (hb : d75225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4783, d75225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4783, d75225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4784 q = 1) (hb : d75226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4784, d75226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4784, d75226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69787 q = 1) (hb : d75232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69787, d75232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69787, d75232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7131 (p : Pattern) (ha : d69797 p = 1) (hb : d75241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d720 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85 q ha hb
    | true =>
      simp only [d720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52393 q = 1) (hb : d69793 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69794 q = 1) (hb : d75238 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69794, d75238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69794, d75238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69795 q = 1) (hb : d75239 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69795, d75239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69795, d75239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69796 q = 1) (hb : d75240 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69796, d75240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69796, d75240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69797 q = 1) (hb : d75241 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69797, d75241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69797, d75241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7132 (p : Pattern) (ha : d69803 p = 1) (hb : d75247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4786 q = 1) (hb : d75228 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4786, d75228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7128 q ha hb
    | true =>
      simp only [d4786, d75228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7129 q ha hb
  have h2 (q : Pattern) (ha : d4787 q = 1) (hb : d75229 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4787, d75229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4787, d75229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69785 q = 1) (hb : d75230 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69785, d75230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69785, d75230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69786 q = 1) (hb : d75231 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69786, d75231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69786, d75231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69788 q = 1) (hb : d75233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69788, d75233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69788, d75233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7130 q ha hb
  have h6 (q : Pattern) (ha : d69789 q = 1) (hb : d75234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69789, d75234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69789, d75234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69790 q = 1) (hb : d75235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69790, d75235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69790, d75235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69791 q = 1) (hb : d75236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69791, d75236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69791, d75236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69792 q = 1) (hb : d75237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69792, d75237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69792, d75237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69798 q = 1) (hb : d75242 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69798, d75242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69798, d75242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7131 q ha hb
  have h11 (q : Pattern) (ha : d69799 q = 1) (hb : d75243 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69799, d75243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69799, d75243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69800 q = 1) (hb : d75244 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69800, d75244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69800, d75244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69801 q = 1) (hb : d75245 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69801, d75245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69801, d75245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69802 q = 1) (hb : d75246 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69802, d75246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69802, d75246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69803 q = 1) (hb : d75247 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69803, d75247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69803, d75247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7133 (p : Pattern) (ha : d69809 p = 1) (hb : d75253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69804 q = 1) (hb : d75248 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69804, d75248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69804, d75248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7132 q ha hb
  have h2 (q : Pattern) (ha : d69805 q = 1) (hb : d75249 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69805, d75249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69805, d75249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69806 q = 1) (hb : d75250 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69806, d75250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69806, d75250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69807 q = 1) (hb : d75251 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69807, d75251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69807, d75251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69808 q = 1) (hb : d75252 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69808, d75252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69808, d75252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69809 q = 1) (hb : d75253 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69809, d75253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69809, d75253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7134 (p : Pattern) (ha : d4873 p = 1) (hb : d75258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d909 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d75255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, d75255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, d75255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d75256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, d75256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, d75256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d75257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, d75257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, d75257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4873 q = 1) (hb : d75258 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4873, d75258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4873, d75258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7135 (p : Pattern) (ha : d4880 p = 1) (hb : d75262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d909 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4869 q = 1) (hb : d52456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4870 q = 1) (hb : d75255 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4870, d75255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4870, d75255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4871 q = 1) (hb : d75256 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4871, d75256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4871, d75256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4872 q = 1) (hb : d75257 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4872, d75257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4872, d75257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d932 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4876 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4877 q = 1) (hb : d75259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, d75259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4877, d75259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4878 q = 1) (hb : d75260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, d75260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, d75260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4879 q = 1) (hb : d75261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, d75261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, d75261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4880 q = 1) (hb : d75262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4880, d75262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4880, d75262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7136 (p : Pattern) (ha : d69813 p = 1) (hb : d75267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d932 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4876 q = 1) (hb : d52469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4877 q = 1) (hb : d75259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4877, d75259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4877, d75259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4878 q = 1) (hb : d75260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4878, d75260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4878, d75260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4879 q = 1) (hb : d75261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4879, d75261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4879, d75261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69813 q = 1) (hb : d75267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69813, d75267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69813, d75267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7137 (p : Pattern) (ha : d69823 p = 1) (hb : d75276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1053 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q ha hb
    | true =>
      simp only [d1053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52630 q = 1) (hb : d69819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69820 q = 1) (hb : d75273 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69820, d75273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69820, d75273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69821 q = 1) (hb : d75274 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69821, d75274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69821, d75274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69822 q = 1) (hb : d75275 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69822, d75275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69822, d75275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69823 q = 1) (hb : d75276 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69823, d75276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69823, d75276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7138 (p : Pattern) (ha : d69829 p = 1) (hb : d75282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4881 q = 1) (hb : d75263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4881, d75263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7134 q ha hb
    | true =>
      simp only [d4881, d75263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7135 q ha hb
  have h2 (q : Pattern) (ha : d4882 q = 1) (hb : d75264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4882, d75264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4882, d75264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69811 q = 1) (hb : d75265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69811, d75265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69811, d75265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69812 q = 1) (hb : d75266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69812, d75266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69812, d75266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69814 q = 1) (hb : d75268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69814, d75268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69814, d75268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7136 q ha hb
  have h6 (q : Pattern) (ha : d69815 q = 1) (hb : d75269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69815, d75269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69815, d75269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69816 q = 1) (hb : d75270 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69816, d75270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69816, d75270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69817 q = 1) (hb : d75271 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69817, d75271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69817, d75271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69818 q = 1) (hb : d75272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69818, d75272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69818, d75272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69824 q = 1) (hb : d75277 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69824, d75277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69824, d75277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7137 q ha hb
  have h11 (q : Pattern) (ha : d69825 q = 1) (hb : d75278 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69825, d75278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69825, d75278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69826 q = 1) (hb : d75279 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69826, d75279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69826, d75279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69827 q = 1) (hb : d75280 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69827, d75280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69827, d75280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69828 q = 1) (hb : d75281 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69828, d75281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69828, d75281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69829 q = 1) (hb : d75282 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69829, d75282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69829, d75282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7139 (p : Pattern) (ha : d69835 p = 1) (hb : d75288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69830 q = 1) (hb : d75283 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69830, d75283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69830, d75283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7138 q ha hb
  have h2 (q : Pattern) (ha : d69831 q = 1) (hb : d75284 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69831, d75284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69831, d75284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69832 q = 1) (hb : d75285 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69832, d75285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69832, d75285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69833 q = 1) (hb : d75286 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69833, d75286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69833, d75286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69834 q = 1) (hb : d75287 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69834, d75287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69834, d75287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69835 q = 1) (hb : d75288 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69835, d75288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69835, d75288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7140 (p : Pattern) (ha : d4969 p = 1) (hb : d75294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1320 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d75291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, d75291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, d75291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d75292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, d75292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, d75292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d75293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, d75293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, d75293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4969 q = 1) (hb : d75294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4969, d75294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4969, d75294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7141 (p : Pattern) (ha : d4976 p = 1) (hb : d75298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1320 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4965 q = 1) (hb : d52739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4966 q = 1) (hb : d75291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4966, d75291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4966, d75291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4967 q = 1) (hb : d75292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4967, d75292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4967, d75292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4968 q = 1) (hb : d75293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4968, d75293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4968, d75293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1343 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4972 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4973 q = 1) (hb : d75295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, d75295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4973, d75295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d4974 q = 1) (hb : d75296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, d75296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, d75296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4975 q = 1) (hb : d75297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, d75297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, d75297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4976 q = 1) (hb : d75298 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4976, d75298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4976, d75298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7142 (p : Pattern) (ha : d69840 p = 1) (hb : d75303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1343 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4972 q = 1) (hb : d52752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4973 q = 1) (hb : d75295 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4973, d75295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4973, d75295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4974 q = 1) (hb : d75296 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4974, d75296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4974, d75296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4975 q = 1) (hb : d75297 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4975, d75297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4975, d75297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69840 q = 1) (hb : d75303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69840, d75303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69840, d75303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7143 (p : Pattern) (ha : d69850 p = 1) (hb : d75312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1487 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q ha hb
    | true =>
      simp only [d1487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52924 q = 1) (hb : d69846 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69847 q = 1) (hb : d75309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69847, d75309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69847, d75309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69848 q = 1) (hb : d75310 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69848, d75310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69848, d75310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69849 q = 1) (hb : d75311 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69849, d75311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69849, d75311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69850 q = 1) (hb : d75312 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69850, d75312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69850, d75312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7144 (p : Pattern) (ha : d69856 p = 1) (hb : d75318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4977 q = 1) (hb : d75299 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4977, d75299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7140 q ha hb
    | true =>
      simp only [d4977, d75299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7141 q ha hb
  have h2 (q : Pattern) (ha : d4978 q = 1) (hb : d75300 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4978, d75300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4978, d75300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69838 q = 1) (hb : d75301 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69838, d75301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69838, d75301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69839 q = 1) (hb : d75302 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69839, d75302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69839, d75302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69841 q = 1) (hb : d75304 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69841, d75304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69841, d75304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7142 q ha hb
  have h6 (q : Pattern) (ha : d69842 q = 1) (hb : d75305 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69842, d75305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69842, d75305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69843 q = 1) (hb : d75306 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69843, d75306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69843, d75306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69844 q = 1) (hb : d75307 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69844, d75307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69844, d75307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69845 q = 1) (hb : d75308 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69845, d75308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69845, d75308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69851 q = 1) (hb : d75313 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69851, d75313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69851, d75313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7143 q ha hb
  have h11 (q : Pattern) (ha : d69852 q = 1) (hb : d75314 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69852, d75314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69852, d75314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69853 q = 1) (hb : d75315 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69853, d75315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69853, d75315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69854 q = 1) (hb : d75316 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69854, d75316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69854, d75316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69855 q = 1) (hb : d75317 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69855, d75317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69855, d75317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69856 q = 1) (hb : d75318 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69856, d75318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69856, d75318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7145 (p : Pattern) (ha : d69862 p = 1) (hb : d75324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69857 q = 1) (hb : d75319 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69857, d75319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69857, d75319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7144 q ha hb
  have h2 (q : Pattern) (ha : d69858 q = 1) (hb : d75320 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69858, d75320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69858, d75320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69859 q = 1) (hb : d75321 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69859, d75321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69859, d75321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69860 q = 1) (hb : d75322 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69860, d75322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69860, d75322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69861 q = 1) (hb : d75323 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69861, d75323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69861, d75323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69862 q = 1) (hb : d75324 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69862, d75324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69862, d75324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7146 (p : Pattern) (ha : d5080 p = 1) (hb : d75331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1797 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d75328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, d75328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, d75328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d75329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, d75329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, d75329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d75330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, d75330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, d75330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5080 q = 1) (hb : d75331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5080, d75331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5080, d75331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7147 (p : Pattern) (ha : d5087 p = 1) (hb : d75335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1797 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5076 q = 1) (hb : d53060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5077 q = 1) (hb : d75328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5077, d75328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5077, d75328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5078 q = 1) (hb : d75329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5078, d75329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5078, d75329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5079 q = 1) (hb : d75330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5079, d75330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5079, d75330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1820 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5083 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5084 q = 1) (hb : d75332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, d75332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5084, d75332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5085 q = 1) (hb : d75333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, d75333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, d75333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5086 q = 1) (hb : d75334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, d75334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, d75334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5087 q = 1) (hb : d75335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5087, d75335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5087, d75335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7148 (p : Pattern) (ha : d69868 p = 1) (hb : d75340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1820 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5083 q = 1) (hb : d53073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5084 q = 1) (hb : d75332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5084, d75332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5084, d75332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5085 q = 1) (hb : d75333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5085, d75333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5085, d75333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5086 q = 1) (hb : d75334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5086, d75334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5086, d75334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69868 q = 1) (hb : d75340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69868, d75340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69868, d75340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7149 (p : Pattern) (ha : d69878 p = 1) (hb : d75349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1964 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q ha hb
    | true =>
      simp only [d1964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53239 q = 1) (hb : d69874 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69875 q = 1) (hb : d75346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69875, d75346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69875, d75346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69876 q = 1) (hb : d75347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69876, d75347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69876, d75347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69877 q = 1) (hb : d75348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69877, d75348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69877, d75348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69878 q = 1) (hb : d75349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69878, d75349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69878, d75349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7150 (p : Pattern) (ha : d69884 p = 1) (hb : d75355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5088 q = 1) (hb : d75336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5088, d75336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7146 q ha hb
    | true =>
      simp only [d5088, d75336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7147 q ha hb
  have h2 (q : Pattern) (ha : d5089 q = 1) (hb : d75337 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5089, d75337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5089, d75337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69866 q = 1) (hb : d75338 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69866, d75338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69866, d75338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69867 q = 1) (hb : d75339 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69867, d75339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69867, d75339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69869 q = 1) (hb : d75341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69869, d75341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69869, d75341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7148 q ha hb
  have h6 (q : Pattern) (ha : d69870 q = 1) (hb : d75342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69870, d75342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69870, d75342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69871 q = 1) (hb : d75343 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69871, d75343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69871, d75343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69872 q = 1) (hb : d75344 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69872, d75344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69872, d75344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69873 q = 1) (hb : d75345 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69873, d75345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69873, d75345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69879 q = 1) (hb : d75350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69879, d75350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69879, d75350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7149 q ha hb
  have h11 (q : Pattern) (ha : d69880 q = 1) (hb : d75351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69880, d75351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69880, d75351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69881 q = 1) (hb : d75352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69881, d75352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69881, d75352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69882 q = 1) (hb : d75353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69882, d75353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69882, d75353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69883 q = 1) (hb : d75354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69883, d75354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69883, d75354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69884 q = 1) (hb : d75355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69884, d75355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69884, d75355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7151 (p : Pattern) (ha : d69890 p = 1) (hb : d75361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69885 q = 1) (hb : d75356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69885, d75356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69885, d75356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7150 q ha hb
  have h2 (q : Pattern) (ha : d69886 q = 1) (hb : d75357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69886, d75357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69886, d75357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69887 q = 1) (hb : d75358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69887, d75358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69887, d75358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69888 q = 1) (hb : d75359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69888, d75359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69888, d75359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69889 q = 1) (hb : d75360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69889, d75360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69889, d75360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69890 q = 1) (hb : d75361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69890, d75361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69890, d75361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7152 (p : Pattern) (ha : d5197 p = 1) (hb : d75369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2275 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d75366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, d75366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, d75366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d75367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, d75367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, d75367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d75368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, d75368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, d75368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5197 q = 1) (hb : d75369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5197, d75369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5197, d75369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7153 (p : Pattern) (ha : d5204 p = 1) (hb : d75373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2275 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5193 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5194 q = 1) (hb : d75366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5194, d75366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5194, d75366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5195 q = 1) (hb : d75367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5195, d75367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5195, d75367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5196 q = 1) (hb : d75368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5196, d75368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5196, d75368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2298 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5200 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5201 q = 1) (hb : d75370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, d75370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5201, d75370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5202 q = 1) (hb : d75371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, d75371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, d75371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5203 q = 1) (hb : d75372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, d75372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, d75372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5204 q = 1) (hb : d75373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5204, d75373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5204, d75373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro7154 (p : Pattern) (ha : d69897 p = 1) (hb : d75378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2298 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5200 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5201 q = 1) (hb : d75370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5201, d75370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5201, d75370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5202 q = 1) (hb : d75371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5202, d75371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5202, d75371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5203 q = 1) (hb : d75372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5203, d75372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5203, d75372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69897 q = 1) (hb : d75378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69897, d75378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69897, d75378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7155 (p : Pattern) (ha : d69907 p = 1) (hb : d75387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2442 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q ha hb
    | true =>
      simp only [d2442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53556 q = 1) (hb : d69903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d69904 q = 1) (hb : d75384 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69904, d75384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69904, d75384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69905 q = 1) (hb : d75385 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69905, d75385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69905, d75385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69906 q = 1) (hb : d75386 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69906, d75386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69906, d75386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69907 q = 1) (hb : d75387 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69907, d75387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69907, d75387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro7156 (p : Pattern) (ha : d69913 p = 1) (hb : d75393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5205 q = 1) (hb : d75374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5205, d75374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7152 q ha hb
    | true =>
      simp only [d5205, d75374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7153 q ha hb
  have h2 (q : Pattern) (ha : d5206 q = 1) (hb : d75375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d5206, d75375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5206, d75375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69895 q = 1) (hb : d75376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69895, d75376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69895, d75376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69896 q = 1) (hb : d75377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69896, d75377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69896, d75377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69898 q = 1) (hb : d75379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69898, d75379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69898, d75379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7154 q ha hb
  have h6 (q : Pattern) (ha : d69899 q = 1) (hb : d75380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69899, d75380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69899, d75380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69900 q = 1) (hb : d75381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69900, d75381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69900, d75381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69901 q = 1) (hb : d75382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69901, d75382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69901, d75382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d69902 q = 1) (hb : d75383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69902, d75383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69902, d75383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69908 q = 1) (hb : d75388 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69908, d75388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69908, d75388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7155 q ha hb
  have h11 (q : Pattern) (ha : d69909 q = 1) (hb : d75389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69909, d75389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69909, d75389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d69910 q = 1) (hb : d75390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69910, d75390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69910, d75390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d69911 q = 1) (hb : d75391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69911, d75391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69911, d75391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d69912 q = 1) (hb : d75392 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69912, d75392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69912, d75392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d69913 q = 1) (hb : d75393 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69913, d75393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69913, d75393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7157 (p : Pattern) (ha : d69919 p = 1) (hb : d75399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69914 q = 1) (hb : d75394 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69914, d75394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69914, d75394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7156 q ha hb
  have h2 (q : Pattern) (ha : d69915 q = 1) (hb : d75395 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69915, d75395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69915, d75395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69916 q = 1) (hb : d75396 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69916, d75396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69916, d75396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69917 q = 1) (hb : d75397 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69917, d75397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69917, d75397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69918 q = 1) (hb : d75398 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69918, d75398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69918, d75398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69919 q = 1) (hb : d75399 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69919, d75399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69919, d75399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7158 (p : Pattern) (ha : d69925 p = 1) (hb : d75405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d69810 q = 1) (hb : d75254 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69810, d75254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7127 q ha hb
    | true =>
      simp only [d69810, d75254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7133 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69836 q = 1) (hb : d75289 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69836, d75289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69836, d75289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7139 q ha hb
  have h3 (q : Pattern) (ha : d69837 q = 1) (hb : d75290 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69837, d75290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69837, d75290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69863 q = 1) (hb : d75325 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69863, d75325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69863, d75325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7145 q ha hb
  have h5 (q : Pattern) (ha : d69864 q = 1) (hb : d75326 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69864, d75326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69864, d75326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69865 q = 1) (hb : d75327 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69865, d75327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69865, d75327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69891 q = 1) (hb : d75362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69891, d75362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69891, d75362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7151 q ha hb
  have h8 (q : Pattern) (ha : d69892 q = 1) (hb : d75363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69892, d75363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69892, d75363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69893 q = 1) (hb : d75364 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69893, d75364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69893, d75364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69894 q = 1) (hb : d75365 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69894, d75365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69894, d75365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69920 q = 1) (hb : d75400 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69920, d75400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69920, d75400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7157 q ha hb
  have h12 (q : Pattern) (ha : d69921 q = 1) (hb : d75401 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69921, d75401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69921, d75401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69922 q = 1) (hb : d75402 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69922, d75402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69922, d75402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69923 q = 1) (hb : d75403 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69923, d75403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69923, d75403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69924 q = 1) (hb : d75404 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69924, d75404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69924, d75404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69925 q = 1) (hb : d75405 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69925, d75405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69925, d75405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7159 (p : Pattern) (ha : d69931 p = 1) (hb : d75411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69926 q = 1) (hb : d75406 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69926, d75406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7158 q ha hb
    | true =>
      simp only [d69926, d75406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69927 q = 1) (hb : d75407 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69927, d75407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69927, d75407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69928 q = 1) (hb : d75408 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69928, d75408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69928, d75408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69929 q = 1) (hb : d75409 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69929, d75409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69929, d75409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69930 q = 1) (hb : d75410 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69930, d75410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69930, d75410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69931 q = 1) (hb : d75411 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69931, d75411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69931, d75411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7160 (p : Pattern) (ha : d69937 p = 1) (hb : d75417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69932 q = 1) (hb : d75412 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69932, d75412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7159 q ha hb
    | true =>
      simp only [d69932, d75412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69933 q = 1) (hb : d75413 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69933, d75413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69933, d75413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69934 q = 1) (hb : d75414 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69934, d75414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69934, d75414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69935 q = 1) (hb : d75415 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69935, d75415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69935, d75415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69936 q = 1) (hb : d75416 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69936, d75416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69936, d75416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69937 q = 1) (hb : d75417 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69937, d75417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69937, d75417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7161 (p : Pattern) (ha : d69943 p = 1) (hb : d75423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69938 q = 1) (hb : d75418 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69938, d75418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7160 q ha hb
    | true =>
      simp only [d69938, d75418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69939 q = 1) (hb : d75419 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69939, d75419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69939, d75419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69940 q = 1) (hb : d75420 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69940, d75420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69940, d75420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69941 q = 1) (hb : d75421 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69941, d75421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69941, d75421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69942 q = 1) (hb : d75422 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69942, d75422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69942, d75422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69943 q = 1) (hb : d75423 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69943, d75423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69943, d75423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7162 (p : Pattern) (ha : d69949 p = 1) (hb : d75429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69944 q = 1) (hb : d75424 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69944, d75424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7161 q ha hb
    | true =>
      simp only [d69944, d75424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69945 q = 1) (hb : d75425 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69945, d75425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69945, d75425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69946 q = 1) (hb : d75426 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69946, d75426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69946, d75426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69947 q = 1) (hb : d75427 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69947, d75427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69947, d75427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69948 q = 1) (hb : d75428 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69948, d75428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69948, d75428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69949 q = 1) (hb : d75429 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69949, d75429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69949, d75429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7163 (p : Pattern) (ha : d69955 p = 1) (hb : d75435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69950 q = 1) (hb : d75430 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69950, d75430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7162 q ha hb
    | true =>
      simp only [d69950, d75430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69951 q = 1) (hb : d75431 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69951, d75431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69951, d75431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69952 q = 1) (hb : d75432 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69952, d75432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69952, d75432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69953 q = 1) (hb : d75433 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69953, d75433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69953, d75433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69954 q = 1) (hb : d75434 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69954, d75434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69954, d75434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69955 q = 1) (hb : d75435 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69955, d75435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69955, d75435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7164 (p : Pattern) (ha : d69961 p = 1) (hb : d75441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69956 q = 1) (hb : d75436 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69956, d75436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7163 q ha hb
    | true =>
      simp only [d69956, d75436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69957 q = 1) (hb : d75437 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69957, d75437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69957, d75437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69958 q = 1) (hb : d75438 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69958, d75438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69958, d75438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69959 q = 1) (hb : d75439 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69959, d75439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69959, d75439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69960 q = 1) (hb : d75440 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69960, d75440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69960, d75440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69961 q = 1) (hb : d75441 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69961, d75441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69961, d75441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7165 (p : Pattern) (ha : d69967 p = 1) (hb : d75447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69962 q = 1) (hb : d75442 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69962, d75442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7164 q ha hb
    | true =>
      simp only [d69962, d75442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69963 q = 1) (hb : d75443 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69963, d75443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69963, d75443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69964 q = 1) (hb : d75444 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69964, d75444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69964, d75444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69965 q = 1) (hb : d75445 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69965, d75445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69965, d75445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69966 q = 1) (hb : d75446 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69966, d75446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69966, d75446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69967 q = 1) (hb : d75447 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69967, d75447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69967, d75447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7166 (p : Pattern) (ha : d69967 p = 1) (hb : d75152 p = 1) : d69967 p = 1 := by
  have h0 (q : Pattern) (ha : d69967 q = 1) (hb : d75152 q = 1) : d69967 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7167 (p : Pattern) (ha : d4339 p = 1) (hb : d73190 p = 1) : d73194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d73190 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4337 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4338 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4339 q = 1) (hb : d73190 q = 1) : d73194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4339, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4339, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7168 (p : Pattern) (ha : d4344 p = 1) (hb : d73190 p = 1) : d73195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d73190, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d73190 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d73190 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4337 q = 1) (hb : d73190 q = 1) : d73192 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4338 q = 1) (hb : d73190 q = 1) : d73193 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4340 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4340, d73190, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d51 q = 1) (hb : d73190 q = 1) : d51 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4341 q = 1) (hb : d73190 q = 1) : d69437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4342 q = 1) (hb : d73190 q = 1) : d69445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4343 q = 1) (hb : d73190 q = 1) : d69446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4344 q = 1) (hb : d73190 q = 1) : d73195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4344, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4344, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7169 (p : Pattern) (ha : d4365 p = 1) (hb : d73190 p = 1) : d73201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4345 q = 1) (hb : d73190 q = 1) : d73196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4345, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7167 q ha hb
    | true =>
      simp only [d4345, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7168 q ha hb
  have h2 (q : Pattern) (ha : d4346 q = 1) (hb : d73190 q = 1) : d73197 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4346, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4346, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4347 q = 1) (hb : d73190 q = 1) : d73198 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4347, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4347, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4348 q = 1) (hb : d73190 q = 1) : d73199 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4348, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4348, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4350 q = 1) (hb : d73190 q = 1) : d69448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5071 q ha hb
  have h6 (q : Pattern) (ha : d4351 q = 1) (hb : d73190 q = 1) : d69449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4351, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4352 q = 1) (hb : d73190 q = 1) : d69450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4353 q = 1) (hb : d73190 q = 1) : d69451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4354 q = 1) (hb : d73190 q = 1) : d73200 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4354, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4354, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4360 q = 1) (hb : d73190 q = 1) : d69457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5072 q ha hb
  have h11 (q : Pattern) (ha : d4361 q = 1) (hb : d73190 q = 1) : d69458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4361, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4362 q = 1) (hb : d73190 q = 1) : d69459 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4363 q = 1) (hb : d73190 q = 1) : d69460 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4364 q = 1) (hb : d73190 q = 1) : d69461 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4365 q = 1) (hb : d73190 q = 1) : d73201 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4365, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4365, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7170 (p : Pattern) (ha : d4375 p = 1) (hb : d73190 p = 1) : d73209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d73190 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d371 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4372 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4373 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4374 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4375 q = 1) (hb : d73190 q = 1) : d73209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4375, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4375, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7171 (p : Pattern) (ha : d4380 p = 1) (hb : d73190 p = 1) : d73210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4371 q = 1) (hb : d73190 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4371, d73190, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d371 q = 1) (hb : d73190 q = 1) : d371 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4372 q = 1) (hb : d73190 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4373 q = 1) (hb : d73190 q = 1) : d73207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4374 q = 1) (hb : d73190 q = 1) : d73208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d385 q = 1) : d385 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d386 q = 1) (hb : d58747 q = 1) : d4725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4376 q = 1) (hb : d73190 q = 1) : d69473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4376, d73190, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d391 q = 1) (hb : d73190 q = 1) : d391 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4377 q = 1) (hb : d73190 q = 1) : d69474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4378 q = 1) (hb : d73190 q = 1) : d69482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4379 q = 1) (hb : d73190 q = 1) : d69483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4380 q = 1) (hb : d73190 q = 1) : d73210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4380, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4380, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7172 (p : Pattern) (ha : d4401 p = 1) (hb : d73190 p = 1) : d73216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4381 q = 1) (hb : d73190 q = 1) : d73211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4381, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7170 q ha hb
    | true =>
      simp only [d4381, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7171 q ha hb
  have h2 (q : Pattern) (ha : d4382 q = 1) (hb : d73190 q = 1) : d73212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4382, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4382, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4383 q = 1) (hb : d73190 q = 1) : d73213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4383, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4383, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4384 q = 1) (hb : d73190 q = 1) : d73214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4384, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4384, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4386 q = 1) (hb : d73190 q = 1) : d69485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5078 q ha hb
  have h6 (q : Pattern) (ha : d4387 q = 1) (hb : d73190 q = 1) : d69486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4387, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4388 q = 1) (hb : d73190 q = 1) : d69487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4389 q = 1) (hb : d73190 q = 1) : d69488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4390 q = 1) (hb : d73190 q = 1) : d73215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4390, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4390, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4396 q = 1) (hb : d73190 q = 1) : d69495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5079 q ha hb
  have h11 (q : Pattern) (ha : d4397 q = 1) (hb : d73190 q = 1) : d69496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4397, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4398 q = 1) (hb : d73190 q = 1) : d69497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4399 q = 1) (hb : d73190 q = 1) : d69498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4400 q = 1) (hb : d73190 q = 1) : d69499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4401 q = 1) (hb : d73190 q = 1) : d73216 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4401, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4401, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7173 (p : Pattern) (ha : d4407 p = 1) (hb : d73190 p = 1) : d73222 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d73190 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4366 q = 1) (hb : d73190 q = 1) : d73202 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4366, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4366, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7169 q ha hb
  have h3 (q : Pattern) (ha : d4367 q = 1) (hb : d73190 q = 1) : d73203 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4367, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4367, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4368 q = 1) (hb : d73190 q = 1) : d73204 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4368, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4368, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4369 q = 1) (hb : d73190 q = 1) : d73205 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4369, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4369, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4370 q = 1) (hb : d73190 q = 1) : d73206 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4370, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4370, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4402 q = 1) (hb : d73190 q = 1) : d73217 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4402, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4402, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7172 q ha hb
  have h8 (q : Pattern) (ha : d4403 q = 1) (hb : d73190 q = 1) : d73218 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4403, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4403, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4404 q = 1) (hb : d73190 q = 1) : d73219 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4404, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4404, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4405 q = 1) (hb : d73190 q = 1) : d73220 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4405, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4405, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4406 q = 1) (hb : d73190 q = 1) : d73221 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4406, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4406, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4407 q = 1) (hb : d73190 q = 1) : d73222 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4407, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4407, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7174 (p : Pattern) (ha : d4412 p = 1) (hb : d73190 p = 1) : d73225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d73190 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d604 q = 1) (hb : d73190 q = 1) : d604 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4409 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4410 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4411 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4412 q = 1) (hb : d73190 q = 1) : d73225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4412, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4412, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7175 (p : Pattern) (ha : d4417 p = 1) (hb : d73190 p = 1) : d73226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d73190 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4408, d73190, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d604 q = 1) (hb : d73190 q = 1) : d604 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4409 q = 1) (hb : d73190 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4410 q = 1) (hb : d73190 q = 1) : d73223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4411 q = 1) (hb : d73190 q = 1) : d73224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d620 q = 1) : d620 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d621 q = 1) (hb : d58747 q = 1) : d4810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4413 q = 1) (hb : d73190 q = 1) : d69512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4413, d73190, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d627 q = 1) (hb : d73190 q = 1) : d627 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4414 q = 1) (hb : d73190 q = 1) : d69513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4415 q = 1) (hb : d73190 q = 1) : d69521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4416 q = 1) (hb : d73190 q = 1) : d69522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4417 q = 1) (hb : d73190 q = 1) : d73226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4417, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4417, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7176 (p : Pattern) (ha : d4438 p = 1) (hb : d73190 p = 1) : d73232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4418 q = 1) (hb : d73190 q = 1) : d73227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4418, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7174 q ha hb
    | true =>
      simp only [d4418, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7175 q ha hb
  have h2 (q : Pattern) (ha : d4419 q = 1) (hb : d73190 q = 1) : d73228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4419, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4419, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4420 q = 1) (hb : d73190 q = 1) : d73229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4420, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4420, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4421 q = 1) (hb : d73190 q = 1) : d73230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4421, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4421, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4423 q = 1) (hb : d73190 q = 1) : d69524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5086 q ha hb
  have h6 (q : Pattern) (ha : d4424 q = 1) (hb : d73190 q = 1) : d69525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4424, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4425 q = 1) (hb : d73190 q = 1) : d69526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4426 q = 1) (hb : d73190 q = 1) : d69527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4427 q = 1) (hb : d73190 q = 1) : d73231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4427, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4427, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4433 q = 1) (hb : d73190 q = 1) : d69534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5087 q ha hb
  have h11 (q : Pattern) (ha : d4434 q = 1) (hb : d73190 q = 1) : d69535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4434, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4435 q = 1) (hb : d73190 q = 1) : d69536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4436 q = 1) (hb : d73190 q = 1) : d69537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4437 q = 1) (hb : d73190 q = 1) : d69538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4438 q = 1) (hb : d73190 q = 1) : d73232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4438, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4438, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7177 (p : Pattern) (ha : d4444 p = 1) (hb : d73190 p = 1) : d73238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4439 q = 1) (hb : d73190 q = 1) : d73233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4439, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4439, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7176 q ha hb
  have h2 (q : Pattern) (ha : d4440 q = 1) (hb : d73190 q = 1) : d73234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4440, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4440, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4441 q = 1) (hb : d73190 q = 1) : d73235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4441, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4441, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4442 q = 1) (hb : d73190 q = 1) : d73236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4442, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4442, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4443 q = 1) (hb : d73190 q = 1) : d73237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4443, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4443, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4444 q = 1) (hb : d73190 q = 1) : d73238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4444, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4444, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7178 (p : Pattern) (ha : d4450 p = 1) (hb : d73190 p = 1) : d73242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d73190 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d910 q = 1) (hb : d73190 q = 1) : d910 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4447 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4448 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4449 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4450 q = 1) (hb : d73190 q = 1) : d73242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4450, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4450, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7179 (p : Pattern) (ha : d4455 p = 1) (hb : d73190 p = 1) : d73243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d73190 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4446, d73190, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d910 q = 1) (hb : d73190 q = 1) : d910 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4447 q = 1) (hb : d73190 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4448 q = 1) (hb : d73190 q = 1) : d73240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4448, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4448, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4449 q = 1) (hb : d73190 q = 1) : d73241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4449, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4449, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d926 q = 1) : d926 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d927 q = 1) (hb : d58747 q = 1) : d4905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4451 q = 1) (hb : d73190 q = 1) : d69552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4451, d73190, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d933 q = 1) (hb : d73190 q = 1) : d933 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4452 q = 1) (hb : d73190 q = 1) : d69553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4453 q = 1) (hb : d73190 q = 1) : d69561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4454 q = 1) (hb : d73190 q = 1) : d69562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4455 q = 1) (hb : d73190 q = 1) : d73243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4455, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4455, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7180 (p : Pattern) (ha : d4476 p = 1) (hb : d73190 p = 1) : d73249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4456 q = 1) (hb : d73190 q = 1) : d73244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4456, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7178 q ha hb
    | true =>
      simp only [d4456, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7179 q ha hb
  have h2 (q : Pattern) (ha : d4457 q = 1) (hb : d73190 q = 1) : d73245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4457, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4457, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4458 q = 1) (hb : d73190 q = 1) : d73246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4458, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4458, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4459 q = 1) (hb : d73190 q = 1) : d73247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4459, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4459, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4461 q = 1) (hb : d73190 q = 1) : d69564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5094 q ha hb
  have h6 (q : Pattern) (ha : d4462 q = 1) (hb : d73190 q = 1) : d69565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4462, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4463 q = 1) (hb : d73190 q = 1) : d69566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4464 q = 1) (hb : d73190 q = 1) : d69567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4465 q = 1) (hb : d73190 q = 1) : d73248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4465, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4465, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4471 q = 1) (hb : d73190 q = 1) : d69574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5095 q ha hb
  have h11 (q : Pattern) (ha : d4472 q = 1) (hb : d73190 q = 1) : d69575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4472, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4473 q = 1) (hb : d73190 q = 1) : d69576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4474 q = 1) (hb : d73190 q = 1) : d69577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4475 q = 1) (hb : d73190 q = 1) : d69578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4476 q = 1) (hb : d73190 q = 1) : d73249 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4476, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4476, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7181 (p : Pattern) (ha : d4482 p = 1) (hb : d73190 p = 1) : d73255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4477 q = 1) (hb : d73190 q = 1) : d73250 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4477, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4477, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7180 q ha hb
  have h2 (q : Pattern) (ha : d4478 q = 1) (hb : d73190 q = 1) : d73251 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4478, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4478, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4479 q = 1) (hb : d73190 q = 1) : d73252 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4479, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4479, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4480 q = 1) (hb : d73190 q = 1) : d73253 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4480, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4480, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4481 q = 1) (hb : d73190 q = 1) : d73254 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4481, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4481, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4482 q = 1) (hb : d73190 q = 1) : d73255 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4482, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4482, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7182 (p : Pattern) (ha : d4489 p = 1) (hb : d73190 p = 1) : d73260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d73190 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1321 q = 1) (hb : d73190 q = 1) : d1321 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4486 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4487 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4488 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4489 q = 1) (hb : d73190 q = 1) : d73260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4489, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4489, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7183 (p : Pattern) (ha : d4494 p = 1) (hb : d73190 p = 1) : d73261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d73190 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4485, d73190, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1321 q = 1) (hb : d73190 q = 1) : d1321 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4486 q = 1) (hb : d73190 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4487 q = 1) (hb : d73190 q = 1) : d73258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4487, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4487, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4488 q = 1) (hb : d73190 q = 1) : d73259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4488, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4488, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d1337 q = 1) : d1337 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1338 q = 1) (hb : d58747 q = 1) : d5001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d73190 q = 1) : d69593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4490, d73190, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d1344 q = 1) (hb : d73190 q = 1) : d1344 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4491 q = 1) (hb : d73190 q = 1) : d69594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4492 q = 1) (hb : d73190 q = 1) : d69602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4493 q = 1) (hb : d73190 q = 1) : d69603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4494 q = 1) (hb : d73190 q = 1) : d73261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4494, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4494, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7184 (p : Pattern) (ha : d4515 p = 1) (hb : d73190 p = 1) : d73267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4495 q = 1) (hb : d73190 q = 1) : d73262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4495, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7182 q ha hb
    | true =>
      simp only [d4495, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7183 q ha hb
  have h2 (q : Pattern) (ha : d4496 q = 1) (hb : d73190 q = 1) : d73263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4496, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4496, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4497 q = 1) (hb : d73190 q = 1) : d73264 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4497, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4497, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4498 q = 1) (hb : d73190 q = 1) : d73265 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4498, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4498, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4500 q = 1) (hb : d73190 q = 1) : d69605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5102 q ha hb
  have h6 (q : Pattern) (ha : d4501 q = 1) (hb : d73190 q = 1) : d69606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4501, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4502 q = 1) (hb : d73190 q = 1) : d69607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4503 q = 1) (hb : d73190 q = 1) : d69608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4504 q = 1) (hb : d73190 q = 1) : d73266 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4504, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4504, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4510 q = 1) (hb : d73190 q = 1) : d69615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5103 q ha hb
  have h11 (q : Pattern) (ha : d4511 q = 1) (hb : d73190 q = 1) : d69616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4511, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4512 q = 1) (hb : d73190 q = 1) : d69617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4513 q = 1) (hb : d73190 q = 1) : d69618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4514 q = 1) (hb : d73190 q = 1) : d69619 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4515 q = 1) (hb : d73190 q = 1) : d73267 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4515, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4515, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7185 (p : Pattern) (ha : d4521 p = 1) (hb : d73190 p = 1) : d73273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4516 q = 1) (hb : d73190 q = 1) : d73268 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4516, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4516, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7184 q ha hb
  have h2 (q : Pattern) (ha : d4517 q = 1) (hb : d73190 q = 1) : d73269 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4517, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4517, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4518 q = 1) (hb : d73190 q = 1) : d73270 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4518, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4518, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4519 q = 1) (hb : d73190 q = 1) : d73271 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4519, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4519, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4520 q = 1) (hb : d73190 q = 1) : d73272 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4520, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4520, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4521 q = 1) (hb : d73190 q = 1) : d73273 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4521, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4521, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7186 (p : Pattern) (ha : d4529 p = 1) (hb : d73190 p = 1) : d73279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d73190 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1798 q = 1) (hb : d73190 q = 1) : d1798 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4526 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4527 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4528 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4529 q = 1) (hb : d73190 q = 1) : d73279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4529, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4529, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7187 (p : Pattern) (ha : d4534 p = 1) (hb : d73190 p = 1) : d73280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d73190 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4525, d73190, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1798 q = 1) (hb : d73190 q = 1) : d1798 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4526 q = 1) (hb : d73190 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4527 q = 1) (hb : d73190 q = 1) : d73277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4527, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4527, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4528 q = 1) (hb : d73190 q = 1) : d73278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4528, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4528, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d1814 q = 1) : d1814 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1815 q = 1) (hb : d58747 q = 1) : d5112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d73190 q = 1) : d69635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4530, d73190, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d1821 q = 1) (hb : d73190 q = 1) : d1821 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4531 q = 1) (hb : d73190 q = 1) : d69636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4532 q = 1) (hb : d73190 q = 1) : d69644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4533 q = 1) (hb : d73190 q = 1) : d69645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4534 q = 1) (hb : d73190 q = 1) : d73280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4534, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4534, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7188 (p : Pattern) (ha : d4555 p = 1) (hb : d73190 p = 1) : d73286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4535 q = 1) (hb : d73190 q = 1) : d73281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4535, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7186 q ha hb
    | true =>
      simp only [d4535, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7187 q ha hb
  have h2 (q : Pattern) (ha : d4536 q = 1) (hb : d73190 q = 1) : d73282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4536, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4536, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4537 q = 1) (hb : d73190 q = 1) : d73283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4537, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4537, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4538 q = 1) (hb : d73190 q = 1) : d73284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4538, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4538, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4540 q = 1) (hb : d73190 q = 1) : d69647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5110 q ha hb
  have h6 (q : Pattern) (ha : d4541 q = 1) (hb : d73190 q = 1) : d69648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4541, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4542 q = 1) (hb : d73190 q = 1) : d69649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4543 q = 1) (hb : d73190 q = 1) : d69650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4544 q = 1) (hb : d73190 q = 1) : d73285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4544, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4544, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4550 q = 1) (hb : d73190 q = 1) : d69657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5111 q ha hb
  have h11 (q : Pattern) (ha : d4551 q = 1) (hb : d73190 q = 1) : d69658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4551, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4552 q = 1) (hb : d73190 q = 1) : d69659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4553 q = 1) (hb : d73190 q = 1) : d69660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4554 q = 1) (hb : d73190 q = 1) : d69661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4555 q = 1) (hb : d73190 q = 1) : d73286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4555, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4555, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7189 (p : Pattern) (ha : d4561 p = 1) (hb : d73190 p = 1) : d73292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4556 q = 1) (hb : d73190 q = 1) : d73287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4556, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4556, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7188 q ha hb
  have h2 (q : Pattern) (ha : d4557 q = 1) (hb : d73190 q = 1) : d73288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4557, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4557, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4558 q = 1) (hb : d73190 q = 1) : d73289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4558, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4558, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4559 q = 1) (hb : d73190 q = 1) : d73290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4559, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4559, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4560 q = 1) (hb : d73190 q = 1) : d73291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4560, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4560, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4561 q = 1) (hb : d73190 q = 1) : d73292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4561, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4561, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7190 (p : Pattern) (ha : d4570 p = 1) (hb : d73190 p = 1) : d73299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d73190 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2276 q = 1) (hb : d73190 q = 1) : d2276 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4567 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4568 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4569 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4570 q = 1) (hb : d73190 q = 1) : d73299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4570, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4570, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro7191 (p : Pattern) (ha : d4575 p = 1) (hb : d73190 p = 1) : d73300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d73190 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4566, d73190, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2276 q = 1) (hb : d73190 q = 1) : d2276 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4567 q = 1) (hb : d73190 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4568 q = 1) (hb : d73190 q = 1) : d73297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4568, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4568, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4569 q = 1) (hb : d73190 q = 1) : d73298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4569, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4569, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1 q = 1) (hb : d2292 q = 1) : d2292 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d2293 q = 1) (hb : d58747 q = 1) : d5229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d73190 q = 1) : d69678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4571, d73190, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d2299 q = 1) (hb : d73190 q = 1) : d2299 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d4572 q = 1) (hb : d73190 q = 1) : d69679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4573 q = 1) (hb : d73190 q = 1) : d69687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4574 q = 1) (hb : d73190 q = 1) : d69688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d4575 q = 1) (hb : d73190 q = 1) : d73300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4575, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4575, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro7192 (p : Pattern) (ha : d4596 p = 1) (hb : d73190 p = 1) : d73306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4576 q = 1) (hb : d73190 q = 1) : d73301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4576, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7190 q ha hb
    | true =>
      simp only [d4576, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7191 q ha hb
  have h2 (q : Pattern) (ha : d4577 q = 1) (hb : d73190 q = 1) : d73302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4577, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4577, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4578 q = 1) (hb : d73190 q = 1) : d73303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4578, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4578, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4579 q = 1) (hb : d73190 q = 1) : d73304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4579, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4579, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4581 q = 1) (hb : d73190 q = 1) : d69690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5118 q ha hb
  have h6 (q : Pattern) (ha : d4582 q = 1) (hb : d73190 q = 1) : d69691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4582, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4583 q = 1) (hb : d73190 q = 1) : d69692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4583, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4584 q = 1) (hb : d73190 q = 1) : d69693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4584, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4585 q = 1) (hb : d73190 q = 1) : d73305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4585, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4585, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4591 q = 1) (hb : d73190 q = 1) : d69700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5119 q ha hb
  have h11 (q : Pattern) (ha : d4592 q = 1) (hb : d73190 q = 1) : d69701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4592, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4593 q = 1) (hb : d73190 q = 1) : d69702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4593, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4594 q = 1) (hb : d73190 q = 1) : d69703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4594, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4595 q = 1) (hb : d73190 q = 1) : d69704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4595, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4596 q = 1) (hb : d73190 q = 1) : d73306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4596, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4596, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7193 (p : Pattern) (ha : d4602 p = 1) (hb : d73190 p = 1) : d73312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4597 q = 1) (hb : d73190 q = 1) : d73307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4597, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4597, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7192 q ha hb
  have h2 (q : Pattern) (ha : d4598 q = 1) (hb : d73190 q = 1) : d73308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4598, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4598, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4599 q = 1) (hb : d73190 q = 1) : d73309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4599, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4599, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4600 q = 1) (hb : d73190 q = 1) : d73310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4600, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4600, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4601 q = 1) (hb : d73190 q = 1) : d73311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4601, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4601, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4602 q = 1) (hb : d73190 q = 1) : d73312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4602, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4602, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7194 (p : Pattern) (ha : d4608 p = 1) (hb : d73190 p = 1) : d73318 p = 1 := by
  have h0 (q : Pattern) (ha : d4445 q = 1) (hb : d73190 q = 1) : d73239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4445, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7173 q ha hb
    | true =>
      simp only [d4445, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7177 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4483 q = 1) (hb : d73190 q = 1) : d73256 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4483, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4483, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7181 q ha hb
  have h3 (q : Pattern) (ha : d4484 q = 1) (hb : d73190 q = 1) : d73257 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4484, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4484, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4522 q = 1) (hb : d73190 q = 1) : d73274 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4522, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4522, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7185 q ha hb
  have h5 (q : Pattern) (ha : d4523 q = 1) (hb : d73190 q = 1) : d73275 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4523, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4523, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4524 q = 1) (hb : d73190 q = 1) : d73276 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4524, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4524, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4562 q = 1) (hb : d73190 q = 1) : d73293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4562, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4562, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7189 q ha hb
  have h8 (q : Pattern) (ha : d4563 q = 1) (hb : d73190 q = 1) : d73294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4563, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4563, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4564 q = 1) (hb : d73190 q = 1) : d73295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4564, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4564, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4565 q = 1) (hb : d73190 q = 1) : d73296 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4565, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4565, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4603 q = 1) (hb : d73190 q = 1) : d73313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d4603, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4603, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7193 q ha hb
  have h12 (q : Pattern) (ha : d4604 q = 1) (hb : d73190 q = 1) : d73314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d4604, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4604, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4605 q = 1) (hb : d73190 q = 1) : d73315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d4605, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4605, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4606 q = 1) (hb : d73190 q = 1) : d73316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d4606, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4606, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d4607 q = 1) (hb : d73190 q = 1) : d73317 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d4607, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4607, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4608 q = 1) (hb : d73190 q = 1) : d73318 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d4608, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4608, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro7195 (p : Pattern) (ha : d4614 p = 1) (hb : d73190 p = 1) : d73324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4609 q = 1) (hb : d73190 q = 1) : d73319 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d4609, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7194 q ha hb
    | true =>
      simp only [d4609, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4610 q = 1) (hb : d73190 q = 1) : d73320 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d4610, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4610, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4611 q = 1) (hb : d73190 q = 1) : d73321 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d4611, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4611, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4612 q = 1) (hb : d73190 q = 1) : d73322 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d4612, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4612, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4613 q = 1) (hb : d73190 q = 1) : d73323 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d4613, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4613, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4614 q = 1) (hb : d73190 q = 1) : d73324 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d4614, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4614, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7196 (p : Pattern) (ha : d4620 p = 1) (hb : d73190 p = 1) : d73330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4615 q = 1) (hb : d73190 q = 1) : d73325 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d4615, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7195 q ha hb
    | true =>
      simp only [d4615, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4616 q = 1) (hb : d73190 q = 1) : d73326 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d4616, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4616, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4617 q = 1) (hb : d73190 q = 1) : d73327 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d4617, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4617, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4618 q = 1) (hb : d73190 q = 1) : d73328 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d4618, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4618, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4619 q = 1) (hb : d73190 q = 1) : d73329 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d4619, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4619, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4620 q = 1) (hb : d73190 q = 1) : d73330 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d4620, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4620, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7197 (p : Pattern) (ha : d4626 p = 1) (hb : d73190 p = 1) : d73336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4621 q = 1) (hb : d73190 q = 1) : d73331 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d4621, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7196 q ha hb
    | true =>
      simp only [d4621, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4622 q = 1) (hb : d73190 q = 1) : d73332 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d4622, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4622, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4623 q = 1) (hb : d73190 q = 1) : d73333 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d4623, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4623, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4624 q = 1) (hb : d73190 q = 1) : d73334 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d4624, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4624, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4625 q = 1) (hb : d73190 q = 1) : d73335 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4625, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4625, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4626 q = 1) (hb : d73190 q = 1) : d73336 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4626, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4626, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7198 (p : Pattern) (ha : d4632 p = 1) (hb : d73190 p = 1) : d73342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4627 q = 1) (hb : d73190 q = 1) : d73337 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4627, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7197 q ha hb
    | true =>
      simp only [d4627, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4628 q = 1) (hb : d73190 q = 1) : d73338 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4628, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4628, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4629 q = 1) (hb : d73190 q = 1) : d73339 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4629, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4629, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4630 q = 1) (hb : d73190 q = 1) : d73340 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4630, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4630, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4631 q = 1) (hb : d73190 q = 1) : d73341 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4631, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4631, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4632 q = 1) (hb : d73190 q = 1) : d73342 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4632, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4632, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7199 (p : Pattern) (ha : d4638 p = 1) (hb : d73190 p = 1) : d73348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4633 q = 1) (hb : d73190 q = 1) : d73343 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4633, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7198 q ha hb
    | true =>
      simp only [d4633, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4634 q = 1) (hb : d73190 q = 1) : d73344 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4634, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4634, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4635 q = 1) (hb : d73190 q = 1) : d73345 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4635, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4635, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4636 q = 1) (hb : d73190 q = 1) : d73346 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4636, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4636, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4637 q = 1) (hb : d73190 q = 1) : d73347 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4637, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4637, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4638 q = 1) (hb : d73190 q = 1) : d73348 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4638, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4638, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7200 (p : Pattern) (ha : d4644 p = 1) (hb : d73190 p = 1) : d73354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4639 q = 1) (hb : d73190 q = 1) : d73349 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4639, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7199 q ha hb
    | true =>
      simp only [d4639, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4640 q = 1) (hb : d73190 q = 1) : d73350 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4640, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4640, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4641 q = 1) (hb : d73190 q = 1) : d73351 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4641, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4641, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4642 q = 1) (hb : d73190 q = 1) : d73352 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4642, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4642, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4643 q = 1) (hb : d73190 q = 1) : d73353 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4643, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4643, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4644 q = 1) (hb : d73190 q = 1) : d73354 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4644, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4644, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7201 (p : Pattern) (ha : d4650 p = 1) (hb : d73190 p = 1) : d73360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4645 q = 1) (hb : d73190 q = 1) : d73355 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4645, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7200 q ha hb
    | true =>
      simp only [d4645, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4646 q = 1) (hb : d73190 q = 1) : d73356 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4646, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4646, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4647 q = 1) (hb : d73190 q = 1) : d73357 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4647, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4647, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4648 q = 1) (hb : d73190 q = 1) : d73358 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4648, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4648, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4649 q = 1) (hb : d73190 q = 1) : d73359 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4649, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4649, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4650 q = 1) (hb : d73190 q = 1) : d73360 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4650, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4650, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro7202 (p : Pattern) (ha : d68756 p = 1) (hb : d73194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d68752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d68752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d371, d68752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d68753 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68753, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68753, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68754 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68754, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68754, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68755 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68755, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68755, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68756 q = 1) (hb : d73194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68756, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68756, d73194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7203 (p : Pattern) (ha : d68761 p = 1) (hb : d73195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d371 q = 1) (hb : d68752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d68752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d371, d68752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d68753 q = 1) (hb : d69433 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68753, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68753, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68754 q = 1) (hb : d73192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68754, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68754, d73192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68755 q = 1) (hb : d73193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68755, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68755, d73193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d391 q = 1) (hb : d68757 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d68757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d391, d68757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d68758 q = 1) (hb : d69437 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68758, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d68758, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d68759 q = 1) (hb : d69445 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68759, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d68759, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d68760 q = 1) (hb : d69446 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68760, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d68760, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d68761 q = 1) (hb : d73195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68761, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68761, d73195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7204 (p : Pattern) (ha : d68784 p = 1) (hb : d73201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68762 q = 1) (hb : d73196 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68762, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7202 q ha hb
    | true =>
      simp only [d68762, d73196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d68763 q = 1) (hb : d73197 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68763, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68763, d73197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68764 q = 1) (hb : d73198 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68764, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68764, d73198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68765 q = 1) (hb : d73199 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68765, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68765, d73199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68769 q = 1) (hb : d69448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68769, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68769, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4262 q ha hb
  have h8 (q : Pattern) (ha : d68770 q = 1) (hb : d69449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68770, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68770, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d68771 q = 1) (hb : d69450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68771, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68771, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d68772 q = 1) (hb : d69451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68772, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68772, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d68773 q = 1) (hb : d73200 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68773, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68773, d73200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68779 q = 1) (hb : d69457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68779, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68779, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4263 q ha hb
  have h13 (q : Pattern) (ha : d68780 q = 1) (hb : d69458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68780, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68780, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d68781 q = 1) (hb : d69459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68781, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68781, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d68782 q = 1) (hb : d69460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68782, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d68782, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d68783 q = 1) (hb : d69461 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68783, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68783, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d68784 q = 1) (hb : d73201 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68784, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68784, d73201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro7205 (p : Pattern) (ha : d68817 p = 1) (hb : d73209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d68811 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4711 q = 1) (hb : d68812 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d68812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d68812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68813 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68813, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68813, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d68814 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68814, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68814, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68815 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68815, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68815, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68816 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68816, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68816, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68817 q = 1) (hb : d73209 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68817, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68817, d73209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7206 (p : Pattern) (ha : d68830 p = 1) (hb : d73210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68808 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4711 q = 1) (hb : d68812 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4711, d68812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d4711, d68812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68813 q = 1) (hb : d69468 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68813, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68813, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d370 q = 1) (hb : d52138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d371 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d68814 q = 1) (hb : d69469 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68814, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68814, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68815 q = 1) (hb : d73207 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68815, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68815, d73207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68816 q = 1) (hb : d73208 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68816, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68816, d73208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d68821 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68824 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4725 q = 1) (hb : d68825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4725, d68825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d4725, d68825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68826 q = 1) (hb : d69473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68826, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d68826, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d390 q = 1) (hb : d52156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d390, d52156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d391 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d391, d52157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d68827 q = 1) (hb : d69474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68827, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68827, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d68828 q = 1) (hb : d69482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68828, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d68828, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d68829 q = 1) (hb : d69483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68829, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d68829, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d68830 q = 1) (hb : d73210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68830, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68830, d73210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7207 (p : Pattern) (ha : d68865 p = 1) (hb : d73216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68804 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68831 q = 1) (hb : d73211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68831, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7205 q ha hb
    | true =>
      simp only [d68831, d73211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7206 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d68842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d68843 q = 1) (hb : d73212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68843, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68843, d73212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68844 q = 1) (hb : d73213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68844, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68844, d73213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68845 q = 1) (hb : d73214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68845, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68845, d73214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68849 q = 1) (hb : d69485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68849, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68849, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4269 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68850 q = 1) (hb : d69486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68850, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68850, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d68851 q = 1) (hb : d69487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68851, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68851, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d68852 q = 1) (hb : d69488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68852, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68852, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d68853 q = 1) (hb : d73215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68853, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68853, d73215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68860 q = 1) (hb : d69495 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68860, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68860, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4270 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68861 q = 1) (hb : d69496 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68861, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68861, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d68862 q = 1) (hb : d69497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68862, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68862, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d68863 q = 1) (hb : d69498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68863, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d68863, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d68864 q = 1) (hb : d69499 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68864, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d68864, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d68865 q = 1) (hb : d73216 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68865, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68865, d73216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7208 (p : Pattern) (ha : d68871 p = 1) (hb : d73222 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d68785 q = 1) (hb : d73202 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68785, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68785, d73202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7204 q ha hb
  have h6 (q : Pattern) (ha : d68786 q = 1) (hb : d73203 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68786, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68786, d73203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68787 q = 1) (hb : d73204 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68787, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68787, d73204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68788 q = 1) (hb : d73205 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68788, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68788, d73205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68789 q = 1) (hb : d73206 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68789, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68789, d73206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68866 q = 1) (hb : d73217 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68866, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68866, d73217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7207 q ha hb
  have h11 (q : Pattern) (ha : d68867 q = 1) (hb : d73218 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68867, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68867, d73218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68868 q = 1) (hb : d73219 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68868, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68868, d73219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68869 q = 1) (hb : d73220 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68869, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68869, d73220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68870 q = 1) (hb : d73221 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68870, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68870, d73221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68871 q = 1) (hb : d73222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68871, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68871, d73222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7209 (p : Pattern) (ha : d68899 p = 1) (hb : d73225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d68893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4796 q = 1) (hb : d68894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d68894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d68894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68895 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68895, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68895, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d68896 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68896, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68896, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68897 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68897, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68897, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68898 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68898, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68898, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68899 q = 1) (hb : d73225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68899, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68899, d73225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7210 (p : Pattern) (ha : d68912 p = 1) (hb : d73226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68890 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4796 q = 1) (hb : d68894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4796, d68894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d4796, d68894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68895 q = 1) (hb : d69507 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68895, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68895, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d603 q = 1) (hb : d52310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d604 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d68896 q = 1) (hb : d69508 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68896, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68896, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68897 q = 1) (hb : d73223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68897, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68897, d73223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68898 q = 1) (hb : d73224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68898, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68898, d73224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d68903 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68906 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4810 q = 1) (hb : d68907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4810, d68907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d4810, d68907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68908 q = 1) (hb : d69512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68908, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d68908, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d626 q = 1) (hb : d52330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
    | true =>
      simp only [d626, d52330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d627 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d627, d52331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d68909 q = 1) (hb : d69513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68909, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68909, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d68910 q = 1) (hb : d69521 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68910, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d68910, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d68911 q = 1) (hb : d69522 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68911, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d68911, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d68912 q = 1) (hb : d73226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68912, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68912, d73226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7211 (p : Pattern) (ha : d68956 p = 1) (hb : d73232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68886 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68913 q = 1) (hb : d73227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68913, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7209 q ha hb
    | true =>
      simp only [d68913, d73227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7210 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d68933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d68934 q = 1) (hb : d73228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68934, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68934, d73228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68935 q = 1) (hb : d73229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68935, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68935, d73229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68936 q = 1) (hb : d73230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68936, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68936, d73230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68940 q = 1) (hb : d69524 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68940, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68940, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4277 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d68941 q = 1) (hb : d69525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68941, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68941, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d68942 q = 1) (hb : d69526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68942, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68942, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d68943 q = 1) (hb : d69527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68943, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68943, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d68944 q = 1) (hb : d73231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68944, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68944, d73231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68951 q = 1) (hb : d69534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68951, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68951, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4278 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68952 q = 1) (hb : d69535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68952, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68952, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d68953 q = 1) (hb : d69536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68953, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68953, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d68954 q = 1) (hb : d69537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68954, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d68954, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d68955 q = 1) (hb : d69538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68955, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d68955, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d68956 q = 1) (hb : d73232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68956, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68956, d73232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7212 (p : Pattern) (ha : d68962 p = 1) (hb : d73238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68957 q = 1) (hb : d73233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68957, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68957, d73233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7211 q ha hb
  have h2 (q : Pattern) (ha : d68958 q = 1) (hb : d73234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68958, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68958, d73234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68959 q = 1) (hb : d73235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68959, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68959, d73235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68960 q = 1) (hb : d73236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68960, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68960, d73236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68961 q = 1) (hb : d73237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68961, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68961, d73237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68962 q = 1) (hb : d73238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68962, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68962, d73238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7213 (p : Pattern) (ha : d68991 p = 1) (hb : d73242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d68985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4891 q = 1) (hb : d68986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d68986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d68986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68987 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68987, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68987, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d68988 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68988, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68988, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68989 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68989, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d68989, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68990 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68990, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68990, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68991 q = 1) (hb : d73242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68991, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68991, d73242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7214 (p : Pattern) (ha : d69004 p = 1) (hb : d73243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68985 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4891 q = 1) (hb : d68986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4891, d68986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d4891, d68986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d68987 q = 1) (hb : d69547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d68987, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d68987, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d68988 q = 1) (hb : d69548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d68988, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68988, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d68989 q = 1) (hb : d73240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68989, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68989, d73240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68990 q = 1) (hb : d73241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68990, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68990, d73241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d68995 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d68998 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4905 q = 1) (hb : d68999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4905, d68999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d4905, d68999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69000 q = 1) (hb : d69552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69000, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d69000, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d932 q = 1) (hb : d52551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
    | true =>
      simp only [d932, d52551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d933 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d933, d52552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d69001 q = 1) (hb : d69553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69001, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69001, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d69002 q = 1) (hb : d69561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69002, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d69002, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69003 q = 1) (hb : d69562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69003, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69003, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69004 q = 1) (hb : d73243 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69004, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69004, d73243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7215 (p : Pattern) (ha : d69048 p = 1) (hb : d73249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69005 q = 1) (hb : d73244 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69005, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7213 q ha hb
    | true =>
      simp only [d69005, d73244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7214 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69026 q = 1) (hb : d73245 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69026, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69026, d73245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69027 q = 1) (hb : d73246 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69027, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69027, d73246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69028 q = 1) (hb : d73247 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69028, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69028, d73247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69032 q = 1) (hb : d69564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69032, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69032, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4285 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69033 q = 1) (hb : d69565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69033, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69033, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69034 q = 1) (hb : d69566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69034, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69034, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d69035 q = 1) (hb : d69567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69035, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69035, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d69036 q = 1) (hb : d73248 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69036, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69036, d73248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69043 q = 1) (hb : d69574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69043, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69043, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4286 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69044 q = 1) (hb : d69575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69044, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69044, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69045 q = 1) (hb : d69576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69045, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69045, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d69046 q = 1) (hb : d69577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69046, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69046, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d69047 q = 1) (hb : d69578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69047, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69047, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d69048 q = 1) (hb : d73249 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69048, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69048, d73249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7216 (p : Pattern) (ha : d69054 p = 1) (hb : d73255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69049 q = 1) (hb : d73250 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69049, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69049, d73250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7215 q ha hb
  have h2 (q : Pattern) (ha : d69050 q = 1) (hb : d73251 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69050, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69050, d73251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69051 q = 1) (hb : d73252 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69051, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69051, d73252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69052 q = 1) (hb : d73253 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69052, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69052, d73253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69053 q = 1) (hb : d73254 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69053, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69053, d73254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69054 q = 1) (hb : d73255 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69054, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69054, d73255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7217 (p : Pattern) (ha : d69084 p = 1) (hb : d73260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69075 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69078 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4987 q = 1) (hb : d69079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d69079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d69079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69080 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69080, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69080, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69081 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69081, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69081, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69082 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69082, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69082, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69083 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69083, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69083, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69084 q = 1) (hb : d73260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69084, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69084, d73260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7218 (p : Pattern) (ha : d69097 p = 1) (hb : d73261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4987 q = 1) (hb : d69079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4987, d69079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d4987, d69079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69080 q = 1) (hb : d69588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69080, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69080, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d69081 q = 1) (hb : d69589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69081, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69081, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69082 q = 1) (hb : d73258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69082, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69082, d73258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69083 q = 1) (hb : d73259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69083, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69083, d73259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d69088 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69091 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5001 q = 1) (hb : d69092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5001, d69092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d5001, d69092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69093 q = 1) (hb : d69593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69093, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d69093, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d1343 q = 1) (hb : d52831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
    | true =>
      simp only [d1343, d52831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d1344 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1344, d52832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d69094 q = 1) (hb : d69594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69094, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69094, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d69095 q = 1) (hb : d69602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69095, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d69095, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69096 q = 1) (hb : d69603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69096, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69096, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69097 q = 1) (hb : d73261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69097, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69097, d73261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7219 (p : Pattern) (ha : d69155 p = 1) (hb : d73267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69098 q = 1) (hb : d73262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69098, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7217 q ha hb
    | true =>
      simp only [d69098, d73262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7218 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69132 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69133 q = 1) (hb : d73263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69133, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69133, d73263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69134 q = 1) (hb : d73264 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69134, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69134, d73264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69135 q = 1) (hb : d73265 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69135, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69135, d73265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69139 q = 1) (hb : d69605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69139, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69139, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4293 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69140 q = 1) (hb : d69606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69140, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69140, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69141 q = 1) (hb : d69607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69141, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69141, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d69142 q = 1) (hb : d69608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69142, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69142, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d69143 q = 1) (hb : d73266 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69143, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69143, d73266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69150 q = 1) (hb : d69615 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69150, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69150, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4294 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69151 q = 1) (hb : d69616 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69151, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69151, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69152 q = 1) (hb : d69617 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69152, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69152, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d69153 q = 1) (hb : d69618 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69153, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69153, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d69154 q = 1) (hb : d69619 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69154, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69154, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d69155 q = 1) (hb : d73267 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69155, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69155, d73267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7220 (p : Pattern) (ha : d69161 p = 1) (hb : d73273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69156 q = 1) (hb : d73268 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69156, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69156, d73268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7219 q ha hb
  have h2 (q : Pattern) (ha : d69157 q = 1) (hb : d73269 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69157, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69157, d73269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69158 q = 1) (hb : d73270 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69158, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69158, d73270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69159 q = 1) (hb : d73271 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69159, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69159, d73271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69160 q = 1) (hb : d73272 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69160, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69160, d73272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69161 q = 1) (hb : d73273 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69161, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69161, d73273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7221 (p : Pattern) (ha : d69192 p = 1) (hb : d73279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69183 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5098 q = 1) (hb : d69187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d69187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d69187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69188 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69188, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69188, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69189 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69189, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69189, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69190 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69190, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69190, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69191 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69191, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69191, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69192 q = 1) (hb : d73279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69192, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69192, d73279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7222 (p : Pattern) (ha : d69205 p = 1) (hb : d73280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69183 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69186 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5098 q = 1) (hb : d69187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5098, d69187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d5098, d69187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69188 q = 1) (hb : d69630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69188, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69188, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d69189 q = 1) (hb : d69631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69189, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69189, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69190 q = 1) (hb : d73277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69190, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69190, d73277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69191 q = 1) (hb : d73278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69191, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69191, d73278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d69196 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69199 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5112 q = 1) (hb : d69200 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5112, d69200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d5112, d69200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69201 q = 1) (hb : d69635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69201, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d69201, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d1820 q = 1) (hb : d53146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
    | true =>
      simp only [d1820, d53146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d1821 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1821, d53147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d69202 q = 1) (hb : d69636 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69202, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69202, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d69203 q = 1) (hb : d69644 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69203, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d69203, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69204 q = 1) (hb : d69645 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69204, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69204, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69205 q = 1) (hb : d73280 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69205, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69205, d73280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7223 (p : Pattern) (ha : d69268 p = 1) (hb : d73286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69179 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69206 q = 1) (hb : d73281 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69206, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7221 q ha hb
    | true =>
      simp only [d69206, d73281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7222 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69246 q = 1) (hb : d73282 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69246, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69246, d73282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69247 q = 1) (hb : d73283 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69247, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69247, d73283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69248 q = 1) (hb : d73284 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69248, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69248, d73284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69252 q = 1) (hb : d69647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69252, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69252, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4301 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69253 q = 1) (hb : d69648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69253, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69253, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69254 q = 1) (hb : d69649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69254, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69254, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d69255 q = 1) (hb : d69650 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69255, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69255, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d69256 q = 1) (hb : d73285 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69256, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69256, d73285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69263 q = 1) (hb : d69657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69263, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69263, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4302 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69264 q = 1) (hb : d69658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69264, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69264, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69265 q = 1) (hb : d69659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69265, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69265, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d69266 q = 1) (hb : d69660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69266, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69266, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d69267 q = 1) (hb : d69661 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69267, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69267, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d69268 q = 1) (hb : d73286 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69268, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69268, d73286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7224 (p : Pattern) (ha : d69274 p = 1) (hb : d73292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69269 q = 1) (hb : d73287 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69269, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69269, d73287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7223 q ha hb
  have h2 (q : Pattern) (ha : d69270 q = 1) (hb : d73288 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69270, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69270, d73288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69271 q = 1) (hb : d73289 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69271, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69271, d73289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69272 q = 1) (hb : d73290 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69272, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69272, d73290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69273 q = 1) (hb : d73291 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69273, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69273, d73291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69274 q = 1) (hb : d73292 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69274, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69274, d73292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7225 (p : Pattern) (ha : d69306 p = 1) (hb : d73299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69297 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69300 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5215 q = 1) (hb : d69301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d69301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d69301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69302 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69302, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69302, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d69303 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69303, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69303, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69304 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69304, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d69304, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69305 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69305, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69305, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69306 q = 1) (hb : d73299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69306, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69306, d73299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7226 (p : Pattern) (ha : d69319 p = 1) (hb : d73300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69297 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5215 q = 1) (hb : d69301 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5215, d69301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d5215, d69301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69302 q = 1) (hb : d69673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69302, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d69302, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d69303 q = 1) (hb : d69674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69303, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69303, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d69304 q = 1) (hb : d73297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69304, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69304, d73297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69305 q = 1) (hb : d73298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69305, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69305, d73298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d69310 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d69313 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d5229 q = 1) (hb : d69314 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5229, d69314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d5229, d69314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69315 q = 1) (hb : d69678 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d69315, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d69315, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d2298 q = 1) (hb : d53463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
    | true =>
      simp only [d2298, d53463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d2299 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d2299, d53464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d69316 q = 1) (hb : d69679 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d69316, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69316, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d69317 q = 1) (hb : d69687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d69317, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d69317, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d69318 q = 1) (hb : d69688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d69318, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d69318, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d69319 q = 1) (hb : d73300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d69319, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69319, d73300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro7227 (p : Pattern) (ha : d69378 p = 1) (hb : d73306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69293 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69320 q = 1) (hb : d73301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69320, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7225 q ha hb
    | true =>
      simp only [d69320, d73301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7226 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d69355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d69356 q = 1) (hb : d73302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69356, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69356, d73302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d69357 q = 1) (hb : d73303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69357, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69357, d73303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d69358 q = 1) (hb : d73304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69358, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69358, d73304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69362 q = 1) (hb : d69690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69362, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69362, d69690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4309 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d69363 q = 1) (hb : d69691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69363, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69363, d69691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d69364 q = 1) (hb : d69692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69364, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d69364, d69692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d69365 q = 1) (hb : d69693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69365, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69365, d69693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d69366 q = 1) (hb : d73305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69366, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69366, d73305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69373 q = 1) (hb : d69700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d69373, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d69373, d69700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4310 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69374 q = 1) (hb : d69701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d69374, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69374, d69701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69375 q = 1) (hb : d69702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d69375, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69375, d69702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d69376 q = 1) (hb : d69703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d69376, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d69376, d69703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d69377 q = 1) (hb : d69704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d69377, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d69377, d69704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d69378 q = 1) (hb : d73306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d69378, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d69378, d73306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro7228 (p : Pattern) (ha : d69384 p = 1) (hb : d73312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69379 q = 1) (hb : d73307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d69379, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69379, d73307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7227 q ha hb
  have h2 (q : Pattern) (ha : d69380 q = 1) (hb : d73308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d69380, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69380, d73308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d69381 q = 1) (hb : d73309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d69381, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69381, d73309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69382 q = 1) (hb : d73310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d69382, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69382, d73310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69383 q = 1) (hb : d73311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d69383, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69383, d73311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69384 q = 1) (hb : d73312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d69384, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69384, d73312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7229 (p : Pattern) (ha : d69390 p = 1) (hb : d73318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68963 q = 1) (hb : d73239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68963, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7208 q ha hb
    | true =>
      simp only [d68963, d73239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7212 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69055 q = 1) (hb : d73256 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69055, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69055, d73256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7216 q ha hb
  have h3 (q : Pattern) (ha : d69056 q = 1) (hb : d73257 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69056, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d69056, d73257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69162 q = 1) (hb : d73274 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69162, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69162, d73274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7220 q ha hb
  have h5 (q : Pattern) (ha : d69163 q = 1) (hb : d73275 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69163, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69163, d73275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69164 q = 1) (hb : d73276 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69164, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69164, d73276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69275 q = 1) (hb : d73293 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69275, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69275, d73293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7224 q ha hb
  have h8 (q : Pattern) (ha : d69276 q = 1) (hb : d73294 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69276, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69276, d73294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d69277 q = 1) (hb : d73295 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69277, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69277, d73295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69278 q = 1) (hb : d73296 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69278, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69278, d73296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69385 q = 1) (hb : d73313 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d69385, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69385, d73313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7228 q ha hb
  have h12 (q : Pattern) (ha : d69386 q = 1) (hb : d73314 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d69386, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69386, d73314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69387 q = 1) (hb : d73315 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d69387, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69387, d73315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69388 q = 1) (hb : d73316 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d69388, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d69388, d73316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69389 q = 1) (hb : d73317 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d69389, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d69389, d73317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d69390 q = 1) (hb : d73318 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d69390, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d69390, d73318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro7230 (p : Pattern) (ha : d69396 p = 1) (hb : d73324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69391 q = 1) (hb : d73319 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d69391, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7229 q ha hb
    | true =>
      simp only [d69391, d73319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69392 q = 1) (hb : d73320 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d69392, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69392, d73320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69393 q = 1) (hb : d73321 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d69393, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69393, d73321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69394 q = 1) (hb : d73322 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d69394, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69394, d73322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69395 q = 1) (hb : d73323 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d69395, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69395, d73323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69396 q = 1) (hb : d73324 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d69396, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69396, d73324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7231 (p : Pattern) (ha : d69402 p = 1) (hb : d73330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69397 q = 1) (hb : d73325 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d69397, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7230 q ha hb
    | true =>
      simp only [d69397, d73325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69398 q = 1) (hb : d73326 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d69398, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69398, d73326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69399 q = 1) (hb : d73327 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d69399, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69399, d73327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69400 q = 1) (hb : d73328 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d69400, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69400, d73328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69401 q = 1) (hb : d73329 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d69401, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69401, d73329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69402 q = 1) (hb : d73330 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d69402, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69402, d73330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7232 (p : Pattern) (ha : d69408 p = 1) (hb : d73336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69403 q = 1) (hb : d73331 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d69403, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7231 q ha hb
    | true =>
      simp only [d69403, d73331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69404 q = 1) (hb : d73332 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d69404, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69404, d73332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69405 q = 1) (hb : d73333 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d69405, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69405, d73333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69406 q = 1) (hb : d73334 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d69406, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69406, d73334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69407 q = 1) (hb : d73335 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d69407, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69407, d73335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69408 q = 1) (hb : d73336 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d69408, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69408, d73336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7233 (p : Pattern) (ha : d69414 p = 1) (hb : d73342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69409 q = 1) (hb : d73337 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d69409, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7232 q ha hb
    | true =>
      simp only [d69409, d73337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69410 q = 1) (hb : d73338 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d69410, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69410, d73338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69411 q = 1) (hb : d73339 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d69411, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69411, d73339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69412 q = 1) (hb : d73340 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d69412, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69412, d73340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69413 q = 1) (hb : d73341 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d69413, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69413, d73341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69414 q = 1) (hb : d73342 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d69414, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69414, d73342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7234 (p : Pattern) (ha : d69420 p = 1) (hb : d73348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69415 q = 1) (hb : d73343 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69415, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7233 q ha hb
    | true =>
      simp only [d69415, d73343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69416 q = 1) (hb : d73344 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69416, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69416, d73344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69417 q = 1) (hb : d73345 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69417, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69417, d73345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69418 q = 1) (hb : d73346 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69418, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69418, d73346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69419 q = 1) (hb : d73347 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69419, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69419, d73347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69420 q = 1) (hb : d73348 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69420, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69420, d73348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7235 (p : Pattern) (ha : d69426 p = 1) (hb : d73354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69421 q = 1) (hb : d73349 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69421, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7234 q ha hb
    | true =>
      simp only [d69421, d73349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69422 q = 1) (hb : d73350 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69422, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69422, d73350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69423 q = 1) (hb : d73351 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69423, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69423, d73351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69424 q = 1) (hb : d73352 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69424, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69424, d73352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69425 q = 1) (hb : d73353 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69425, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69425, d73353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69426 q = 1) (hb : d73354 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69426, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69426, d73354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7236 (p : Pattern) (ha : d69432 p = 1) (hb : d73360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69427 q = 1) (hb : d73355 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69427, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7235 q ha hb
    | true =>
      simp only [d69427, d73355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d69428 q = 1) (hb : d73356 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69428, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69428, d73356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d69429 q = 1) (hb : d73357 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69429, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69429, d73357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d69430 q = 1) (hb : d73358 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69430, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69430, d73358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69431 q = 1) (hb : d73359 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69431, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69431, d73359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d69432 q = 1) (hb : d73360 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69432, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69432, d73360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro7237 (p : Pattern) (ha : d0 p = 1) (hb : d73190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73190 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7238 (p : Pattern) (ha : d0 p = 1) (hb : d69432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69432 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7239 (p : Pattern) (ha : d0 p = 1) (hb : d70143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70143 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro7240 (p : Pattern) (ha : d4339 p = 1) (hb : d68222 p = 1) : d68542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4335 q = 1) (hb : d68221 q = 1) : d4335 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4336 q = 1) (hb : d68222 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4337 q = 1) (hb : d68222 q = 1) : d68540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4338 q = 1) (hb : d68222 q = 1) : d68541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4339 q = 1) (hb : d68222 q = 1) : d68542 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4339, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4339, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7241 (p : Pattern) (ha : d4344 p = 1) (hb : d68222 p = 1) : d68543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4335 q = 1) (hb : d68221 q = 1) : d4335 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4336 q = 1) (hb : d68222 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4337 q = 1) (hb : d68222 q = 1) : d68540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4337, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4337, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4338 q = 1) (hb : d68222 q = 1) : d68541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4338, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4338, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4340 q = 1) (hb : d68221 q = 1) : d4340 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4341 q = 1) (hb : d68222 q = 1) : d67615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4342 q = 1) (hb : d68222 q = 1) : d67623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4343 q = 1) (hb : d68222 q = 1) : d67624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4344 q = 1) (hb : d68222 q = 1) : d68543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4344, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4344, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7242 (p : Pattern) (ha : d4365 p = 1) (hb : d68222 p = 1) : d68549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4345 q = 1) (hb : d68222 q = 1) : d68544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4345, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7240 q ha hb
    | true =>
      simp only [d4345, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7241 q ha hb
  have h2 (q : Pattern) (ha : d4346 q = 1) (hb : d68222 q = 1) : d68545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4346, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4346, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4347 q = 1) (hb : d68222 q = 1) : d68546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4347, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4347, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4348 q = 1) (hb : d68222 q = 1) : d68547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4348, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4348, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4350 q = 1) (hb : d68222 q = 1) : d67626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4007 q ha hb
  have h6 (q : Pattern) (ha : d4351 q = 1) (hb : d68222 q = 1) : d67627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4351, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4352 q = 1) (hb : d68222 q = 1) : d67628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4352, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4353 q = 1) (hb : d68222 q = 1) : d67629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4353, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4354 q = 1) (hb : d68222 q = 1) : d68548 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4354, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4354, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4360 q = 1) (hb : d68222 q = 1) : d67635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4008 q ha hb
  have h11 (q : Pattern) (ha : d4361 q = 1) (hb : d68222 q = 1) : d67636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4361, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4362 q = 1) (hb : d68222 q = 1) : d67637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4362, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4363 q = 1) (hb : d68222 q = 1) : d67638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4363, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4364 q = 1) (hb : d68222 q = 1) : d67639 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4364, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4365 q = 1) (hb : d68222 q = 1) : d68549 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4365, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4365, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7243 (p : Pattern) (ha : d4375 p = 1) (hb : d68222 p = 1) : d68557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4371 q = 1) (hb : d68221 q = 1) : d4371 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4372 q = 1) (hb : d68222 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4373 q = 1) (hb : d68222 q = 1) : d68555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4374 q = 1) (hb : d68222 q = 1) : d68556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4375 q = 1) (hb : d68222 q = 1) : d68557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4375, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4375, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7244 (p : Pattern) (ha : d4380 p = 1) (hb : d68222 p = 1) : d68558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4371 q = 1) (hb : d68221 q = 1) : d4371 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4372 q = 1) (hb : d68222 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4373 q = 1) (hb : d68222 q = 1) : d68555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4373, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4373, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4374 q = 1) (hb : d68222 q = 1) : d68556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4374, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4374, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4376 q = 1) (hb : d68221 q = 1) : d4376 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4377 q = 1) (hb : d68222 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4378 q = 1) (hb : d68222 q = 1) : d67658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4379 q = 1) (hb : d68222 q = 1) : d67659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4380 q = 1) (hb : d68222 q = 1) : d68558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4380, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4380, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7245 (p : Pattern) (ha : d4401 p = 1) (hb : d68222 p = 1) : d68571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4381 q = 1) (hb : d68222 q = 1) : d68559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4381, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7243 q ha hb
    | true =>
      simp only [d4381, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7244 q ha hb
  have h2 (q : Pattern) (ha : d4382 q = 1) (hb : d68222 q = 1) : d68560 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4382, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4382, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4383 q = 1) (hb : d68222 q = 1) : d68561 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4383, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4383, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4384 q = 1) (hb : d68222 q = 1) : d68562 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4384, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4384, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4386 q = 1) (hb : d68222 q = 1) : d67661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4017 q ha hb
  have h6 (q : Pattern) (ha : d4387 q = 1) (hb : d68222 q = 1) : d68563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4387, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4388 q = 1) (hb : d68222 q = 1) : d68564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4388, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4389 q = 1) (hb : d68222 q = 1) : d68565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4389, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4390 q = 1) (hb : d68222 q = 1) : d68566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4390, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4390, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4396 q = 1) (hb : d68222 q = 1) : d67670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4018 q ha hb
  have h11 (q : Pattern) (ha : d4397 q = 1) (hb : d68222 q = 1) : d68567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4397, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4398 q = 1) (hb : d68222 q = 1) : d68568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4398, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4399 q = 1) (hb : d68222 q = 1) : d68569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4399, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4400 q = 1) (hb : d68222 q = 1) : d68570 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4400, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4401 q = 1) (hb : d68222 q = 1) : d68571 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4401, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4401, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro7246 (p : Pattern) (ha : d4407 p = 1) (hb : d68222 p = 1) : d68577 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d68222 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4366 q = 1) (hb : d68222 q = 1) : d68550 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4366, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4366, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7242 q ha hb
  have h3 (q : Pattern) (ha : d4367 q = 1) (hb : d68222 q = 1) : d68551 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4367, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4367, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4368 q = 1) (hb : d68222 q = 1) : d68552 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4368, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4368, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4369 q = 1) (hb : d68222 q = 1) : d68553 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4369, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4369, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4370 q = 1) (hb : d68222 q = 1) : d68554 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4370, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4370, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4402 q = 1) (hb : d68222 q = 1) : d68572 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d4402, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4402, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7245 q ha hb
  have h8 (q : Pattern) (ha : d4403 q = 1) (hb : d68222 q = 1) : d68573 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d4403, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4403, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4404 q = 1) (hb : d68222 q = 1) : d68574 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d4404, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4404, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4405 q = 1) (hb : d68222 q = 1) : d68575 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d4405, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4405, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4406 q = 1) (hb : d68222 q = 1) : d68576 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d4406, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4406, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4407 q = 1) (hb : d68222 q = 1) : d68577 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d4407, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4407, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro7247 (p : Pattern) (ha : d4412 p = 1) (hb : d68222 p = 1) : d68580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4408 q = 1) (hb : d68221 q = 1) : d4408 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4409 q = 1) (hb : d68222 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4410 q = 1) (hb : d68222 q = 1) : d68578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4411 q = 1) (hb : d68222 q = 1) : d68579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4412 q = 1) (hb : d68222 q = 1) : d68580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4412, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4412, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro7248 (p : Pattern) (ha : d4417 p = 1) (hb : d68222 p = 1) : d68581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4408 q = 1) (hb : d68221 q = 1) : d4408 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4409 q = 1) (hb : d68222 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4410 q = 1) (hb : d68222 q = 1) : d68578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4410, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4410, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4411 q = 1) (hb : d68222 q = 1) : d68579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4411, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4411, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4413 q = 1) (hb : d68221 q = 1) : d4413 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4414 q = 1) (hb : d68222 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d4415 q = 1) (hb : d68222 q = 1) : d67694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4416 q = 1) (hb : d68222 q = 1) : d67695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4417 q = 1) (hb : d68222 q = 1) : d68581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4417, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4417, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro7249 (p : Pattern) (ha : d4438 p = 1) (hb : d68222 p = 1) : d68594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4418 q = 1) (hb : d68222 q = 1) : d68582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4418, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7247 q ha hb
    | true =>
      simp only [d4418, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7248 q ha hb
  have h2 (q : Pattern) (ha : d4419 q = 1) (hb : d68222 q = 1) : d68583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4419, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4419, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4420 q = 1) (hb : d68222 q = 1) : d68584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4420, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4420, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4421 q = 1) (hb : d68222 q = 1) : d68585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4421, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4421, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4423 q = 1) (hb : d68222 q = 1) : d67697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4029 q ha hb
  have h6 (q : Pattern) (ha : d4424 q = 1) (hb : d68222 q = 1) : d68586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4424, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d4425 q = 1) (hb : d68222 q = 1) : d68587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4425, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d4426 q = 1) (hb : d68222 q = 1) : d68588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4426, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d4427 q = 1) (hb : d68222 q = 1) : d68589 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4427, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4427, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4433 q = 1) (hb : d68222 q = 1) : d67706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4030 q ha hb
  have h11 (q : Pattern) (ha : d4434 q = 1) (hb : d68222 q = 1) : d68590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4434, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4435 q = 1) (hb : d68222 q = 1) : d68591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4435, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4436 q = 1) (hb : d68222 q = 1) : d68592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4436, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4437 q = 1) (hb : d68222 q = 1) : d68593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4437, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4438 q = 1) (hb : d68222 q = 1) : d68594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d4438, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4438, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
