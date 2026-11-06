import NetHack.Soko22Hazard87.AndIntroBlocks0249
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro62500 (p : Pattern) (ha : d156724 p = 1) (hb : d247469 p = 1) : d249769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118694 q = 1) (hb : d156618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118694, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118694, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62481 q ha hb
  have h2 (q : Pattern) (ha : d118695 q = 1) (hb : d156619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118695, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118695, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118701 q = 1) (hb : d156625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118701, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62481 q ha hb
    | true =>
      simp only [d118701, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62482 q ha hb
  have h4 (q : Pattern) (ha : d118702 q = 1) (hb : d156626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118702, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118702, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118703 q = 1) (hb : d156627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118703, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118703, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156681 q = 1) (hb : d247429 q = 1) : d249730 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156681, d247429, d249730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62490 q ha hb
    | true =>
      simp only [d156681, d247429, d249730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62494 q ha hb
  have h7 (q : Pattern) (ha : d118757 q = 1) (hb : d156683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118757, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62483 q ha hb
    | true =>
      simp only [d118757, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156684 q = 1) (hb : d247430 q = 1) : d249731 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156684, d247430, d249731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156684, d247430, d249731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d156685 q = 1) (hb : d247431 q = 1) : d249732 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156685, d247431, d249732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156685, d247431, d249732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d156686 q = 1) (hb : d247432 q = 1) : d249733 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156686, d247432, d249733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d156686, d247432, d249733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156690 q = 1) (hb : d247436 q = 1) : d249735 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156690, d247436, d249735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156690, d247436, d249735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62495 q ha hb
  have h12 (q : Pattern) (ha : d156691 q = 1) (hb : d247437 q = 1) : d249736 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156691, d247437, d249736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156691, d247437, d249736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d156692 q = 1) (hb : d247438 q = 1) : d249737 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156692, d247438, d249737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156692, d247438, d249737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d156693 q = 1) (hb : d247439 q = 1) : d249738 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156693, d247439, d249738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156693, d247439, d249738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d156694 q = 1) (hb : d247440 q = 1) : d249739 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156694, d247440, d249739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156694, d247440, d249739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156719 q = 1) (hb : d247464 q = 1) : d249764 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156719, d247464, d249764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156719, d247464, d249764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62499 q ha hb
  have h17 (q : Pattern) (ha : d156720 q = 1) (hb : d247465 q = 1) : d249765 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156720, d247465, d249765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d156720, d247465, d249765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d156721 q = 1) (hb : d247466 q = 1) : d249766 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156721, d247466, d249766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156721, d247466, d249766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d156722 q = 1) (hb : d247467 q = 1) : d249767 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156722, d247467, d249767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d156722, d247467, d249767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d156723 q = 1) (hb : d247468 q = 1) : d249768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156723, d247468, d249768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d156723, d247468, d249768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d156724 q = 1) (hb : d247469 q = 1) : d249769 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d156724, d247469, d249769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156724, d247469, d249769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro62501 (p : Pattern) (ha : d156730 p = 1) (hb : d247475 p = 1) : d249775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118684 q = 1) (hb : d156608 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118684, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118684, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62480 q ha hb
  have h2 (q : Pattern) (ha : d118685 q = 1) (hb : d156609 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118685, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118685, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118686 q = 1) (hb : d156610 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118686, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118686, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118687 q = 1) (hb : d156611 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118687, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118687, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118688 q = 1) (hb : d156612 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118688, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118688, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156725 q = 1) (hb : d247470 q = 1) : d249770 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d156725, d247470, d249770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156725, d247470, d249770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62500 q ha hb
  have h7 (q : Pattern) (ha : d156726 q = 1) (hb : d247471 q = 1) : d249771 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d156726, d247471, d249771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156726, d247471, d249771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156727 q = 1) (hb : d247472 q = 1) : d249772 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d156727, d247472, d249772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156727, d247472, d249772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156728 q = 1) (hb : d247473 q = 1) : d249773 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d156728, d247473, d249773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156728, d247473, d249773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156729 q = 1) (hb : d247474 q = 1) : d249774 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d156729, d247474, d249774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156729, d247474, d249774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156730 q = 1) (hb : d247475 q = 1) : d249775 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d156730, d247475, d249775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d156730, d247475, d249775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62502 (p : Pattern) (ha : d118889 p = 1) (hb : d156818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118639 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q ha hb
    | true =>
      simp only [d118639, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118696 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118696, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118696, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118697 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118697, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118697, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118698 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118698, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118698, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118699 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118699, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118699, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118889 q = 1) (hb : d156818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118889, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118889, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62503 (p : Pattern) (ha : d118929 p = 1) (hb : d156859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118672 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62478 q ha hb
    | true =>
      simp only [d118672, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118925 q = 1) (hb : d156855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118925, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118925, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118926 q = 1) (hb : d156856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118926, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118926, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118927 q = 1) (hb : d156857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118927, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118927, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118928 q = 1) (hb : d156858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118928, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118928, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118929 q = 1) (hb : d156859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118929, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118929, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62504 (p : Pattern) (ha : d156735 p = 1) (hb : d247480 p = 1) : d249780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h2 (q : Pattern) (ha : d156731 q = 1) (hb : d247476 q = 1) : d249776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156732 q = 1) (hb : d247477 q = 1) : d249777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156733 q = 1) (hb : d247478 q = 1) : d249778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156734 q = 1) (hb : d247479 q = 1) : d249779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156735 q = 1) (hb : d247480 q = 1) : d249780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156735, d247480, d249780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156735, d247480, d249780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62505 (p : Pattern) (ha : d156742 p = 1) (hb : d247487 p = 1) : d249787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h2 (q : Pattern) (ha : d156731 q = 1) (hb : d247476 q = 1) : d249776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156732 q = 1) (hb : d247477 q = 1) : d249777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156733 q = 1) (hb : d247478 q = 1) : d249778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156734 q = 1) (hb : d247479 q = 1) : d249779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156675 q = 1) (hb : d247423 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q ha hb
    | true =>
      simp only [d156675, d247423, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62473 q hb ha
  have h7 (q : Pattern) (ha : d156738 q = 1) (hb : d247483 q = 1) : d249783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d247483, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156738, d247483, d249783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156739 q = 1) (hb : d247484 q = 1) : d249784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d247484, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156739, d247484, d249784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d156740 q = 1) (hb : d247485 q = 1) : d249785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d247485, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156740, d247485, d249785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156741 q = 1) (hb : d247486 q = 1) : d249786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d247486, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156741, d247486, d249786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156742 q = 1) (hb : d247487 q = 1) : d249787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156742, d247487, d249787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156742, d247487, d249787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62506 (p : Pattern) (ha : d156809 p = 1) (hb : d247552 p = 1) : d249847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156659 q = 1) (hb : d247416 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q ha hb
    | true =>
      simp only [d156659, d247416, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q hb ha
  have h2 (q : Pattern) (ha : d156731 q = 1) (hb : d247476 q = 1) : d249776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156731, d247476, d249776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156732 q = 1) (hb : d247477 q = 1) : d249777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156732, d247477, d249777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156733 q = 1) (hb : d247478 q = 1) : d249778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156733, d247478, d249778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156734 q = 1) (hb : d247479 q = 1) : d249779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d247479, d249779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118632 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62471 q ha hb
    | true =>
      simp only [d118632, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118689 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118689, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118690 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118690, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118691 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118691, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118692 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118692, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156809 q = 1) (hb : d247552 q = 1) : d249847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156809, d247552, d249847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156809, d247552, d249847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62507 (p : Pattern) (ha : d156747 p = 1) (hb : d247492 p = 1) : d249792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156656 q = 1) (hb : d247413 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156746 q = 1) (hb : d247491 q = 1) : d249791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156746, d247491, d249791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156746, d247491, d249791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156747 q = 1) (hb : d247492 q = 1) : d249792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156747, d247492, d249792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156747, d247492, d249792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62508 (p : Pattern) (ha : d156754 p = 1) (hb : d247499 p = 1) : d249799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156752 q = 1) (hb : d247497 q = 1) : d249797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156752, d247497, d249797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156752, d247497, d249797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156753 q = 1) (hb : d247498 q = 1) : d249798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156753, d247498, d249798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156753, d247498, d249798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156754 q = 1) (hb : d247499 q = 1) : d249799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156754, d247499, d249799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156754, d247499, d249799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62509 (p : Pattern) (ha : d156782 p = 1) (hb : d247525 p = 1) : d249716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156779 q = 1) (hb : d247522 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156779, d247522, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156779, d247522, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156780 q = 1) (hb : d247523 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156780, d247523, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156780, d247523, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156781 q = 1) (hb : d247524 q = 1) : d249715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156781, d247524, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156781, d247524, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d156782 q = 1) (hb : d247525 q = 1) : d249716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156782, d247525, d249716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156782, d247525, d249716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62510 (p : Pattern) (ha : d74175 p = 1) (hb : d248589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25219 q = 1) (hb : d74174 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d74174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25219, d74174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d25220 q = 1) (hb : d74175 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d74175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25220, d74175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d74175 q = 1) (hb : d248589 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62511 (p : Pattern) (ha : d101081 p = 1) (hb : d248584 p = 1) : d249805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101081 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25210 q = 1) (hb : d101079 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25210, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d25435 q = 1) : d25435 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d25436 q = 1) (hb : d101080 q = 1) : d249803 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d101080, d249803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25436, d101080, d249803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25437 q = 1) (hb : d101081 q = 1) : d249804 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d101081, d249804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25437, d101081, d249804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d101081 q = 1) (hb : d248584 q = 1) : d249805 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248584, d249805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248584, d249805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62512 (p : Pattern) (ha : d247507 p = 1) (hb : d248595 p = 1) : d249811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247503 q = 1) (hb : d248585 q = 1) : d249806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
    | true =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247504 q = 1) (hb : d248586 q = 1) : d249807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247505 q = 1) (hb : d248587 q = 1) : d249808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247505, d248587, d249808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247505, d248587, d249808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247506 q = 1) (hb : d248588 q = 1) : d249809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247506, d248588, d249809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247506, d248588, d249809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247399 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247399, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62510 q ha hb
    | true =>
      simp only [d247399, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247400 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247400, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247400, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247401 q = 1) (hb : d248592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247401, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247401, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247402 q = 1) (hb : d248593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247402, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247402, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247507 q = 1) (hb : d248594 q = 1) : d249810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247507, d248594, d249810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247507, d248594, d249810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247507 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d247507 q = 1) (hb : d248595 q = 1) : d249811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248595, d249811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248595, d249811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62513 (p : Pattern) (ha : d247513 p = 1) (hb : d248601 p = 1) : d249817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247508 q = 1) (hb : d248596 q = 1) : d249812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247508, d248596, d249812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62512 q ha hb
    | true =>
      simp only [d247508, d248596, d249812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62487 q hb ha
  have h2 (q : Pattern) (ha : d247509 q = 1) (hb : d248597 q = 1) : d249813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247509, d248597, d249813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247509, d248597, d249813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247510 q = 1) (hb : d248598 q = 1) : d249814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247510, d248598, d249814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247510, d248598, d249814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156647 q = 1) (hb : d247404 q = 1) : d249705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156647, d247404, d249705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62487 q ha hb
    | true =>
      simp only [d156647, d247404, d249705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62469 q hb ha
  have h5 (q : Pattern) (ha : d156648 q = 1) (hb : d247405 q = 1) : d249706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156648, d247405, d249706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156648, d247405, d249706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156649 q = 1) (hb : d247406 q = 1) : d249707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156649, d247406, d249707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156649, d247406, d249707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247511 q = 1) (hb : d248599 q = 1) : d249815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247511, d248599, d249815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247511, d248599, d249815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118620 q = 1) (hb : d156543 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62469 q ha hb
    | true =>
      simp only [d118620, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118621 q = 1) (hb : d156544 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118621, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118622 q = 1) (hb : d156545 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118622, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156650 q = 1) (hb : d247407 q = 1) : d249708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156650, d247407, d249708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156650, d247407, d249708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d247512 q = 1) (hb : d248600 q = 1) : d249816 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247512, d248600, d249816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247512, d248600, d249816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d247513 q = 1) (hb : d248601 q = 1) : d249817 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247513, d248601, d249817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d247513, d248601, d249817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62514 (p : Pattern) (ha : d247519 p = 1) (hb : d248607 p = 1) : d249823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247514 q = 1) (hb : d248602 q = 1) : d249818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247514, d248602, d249818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62513 q ha hb
    | true =>
      simp only [d247514, d248602, d249818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247515 q = 1) (hb : d248603 q = 1) : d249819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247515, d248603, d249819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247515, d248603, d249819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247516 q = 1) (hb : d248604 q = 1) : d249820 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247516, d248604, d249820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247516, d248604, d249820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247517 q = 1) (hb : d248605 q = 1) : d249821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247517, d248605, d249821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247517, d248605, d249821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247518 q = 1) (hb : d248606 q = 1) : d249822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247518, d248606, d249822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247518, d248606, d249822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247519 q = 1) (hb : d248607 q = 1) : d249823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247519, d248607, d249823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247519, d248607, d249823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62515 (p : Pattern) (ha : d247531 p = 1) (hb : d248613 p = 1) : d249829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156748 q = 1) (hb : d247493 q = 1) : d249793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156748, d247493, d249793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62507 q ha hb
    | true =>
      simp only [d156748, d247493, d249793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62484 q hb ha
  have h2 (q : Pattern) (ha : d156749 q = 1) (hb : d247494 q = 1) : d249794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156749, d247494, d249794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156749, d247494, d249794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156750 q = 1) (hb : d247495 q = 1) : d249795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156750, d247495, d249795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156750, d247495, d249795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156751 q = 1) (hb : d247496 q = 1) : d249796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156751, d247496, d249796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156751, d247496, d249796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156755 q = 1) (hb : d247500 q = 1) : d249800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156755, d247500, d249800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62508 q ha hb
    | true =>
      simp only [d156755, d247500, d249800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62485 q hb ha
  have h6 (q : Pattern) (ha : d156756 q = 1) (hb : d247501 q = 1) : d249801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156756, d247501, d249801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156756, d247501, d249801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156757 q = 1) (hb : d247502 q = 1) : d249802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156757, d247502, d249802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156757, d247502, d249802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d247520 q = 1) (hb : d248608 q = 1) : d249824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247520, d248608, d249824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62514 q ha hb
    | true =>
      simp only [d247520, d248608, d249824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247416 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247521 q = 1) (hb : d248609 q = 1) : d249825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247521, d248609, d249825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247521, d248609, d249825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156783 q = 1) (hb : d247526 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156783, d247526, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62509 q ha hb
    | true =>
      simp only [d156783, d247526, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d156784 q = 1) (hb : d247527 q = 1) : d249718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156784, d247527, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156784, d247527, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d247528 q = 1) (hb : d248610 q = 1) : d249826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247528, d248610, d249826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247528, d248610, d249826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d247529 q = 1) (hb : d248611 q = 1) : d249827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247529, d248611, d249827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d247529, d248611, d249827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247530 q = 1) (hb : d248612 q = 1) : d249828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247530, d248612, d249828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d247530, d248612, d249828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247531 q = 1) (hb : d248613 q = 1) : d249829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247531, d248613, d249829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247531, d248613, d249829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62516 (p : Pattern) (ha : d156789 p = 1) (hb : d247532 p = 1) : d249830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156656 q = 1) (hb : d247413 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156656, d247413, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156746 q = 1) (hb : d247491 q = 1) : d249791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156746, d247491, d249791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156746, d247491, d249791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156789 q = 1) (hb : d247532 q = 1) : d249830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156789, d247532, d249830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156789, d247532, d249830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62517 (p : Pattern) (ha : d156794 p = 1) (hb : d247537 p = 1) : d249835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118626 q = 1) (hb : d156549 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62470 q ha hb
    | true =>
      simp only [d118626, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118627 q = 1) (hb : d156550 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118627, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156655 q = 1) (hb : d247412 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156655, d247412, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156752 q = 1) (hb : d247497 q = 1) : d249797 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156752, d247497, d249797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156752, d247497, d249797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156753 q = 1) (hb : d247498 q = 1) : d249798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156753, d247498, d249798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156753, d247498, d249798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d156794 q = 1) (hb : d247537 q = 1) : d249835 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156794, d247537, d249835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156794, d247537, d249835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62518 (p : Pattern) (ha : d156801 p = 1) (hb : d247544 p = 1) : d249723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156779 q = 1) (hb : d247522 q = 1) : d249713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156779, d247522, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156779, d247522, d249713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156780 q = 1) (hb : d247523 q = 1) : d249714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156780, d247523, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156780, d247523, d249714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156781 q = 1) (hb : d247524 q = 1) : d249715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156781, d247524, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156781, d247524, d249715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d156801 q = 1) (hb : d247544 q = 1) : d249723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156801, d247544, d249723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156801, d247544, d249723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62519 (p : Pattern) (ha : d247541 p = 1) (hb : d248614 p = 1) : d249839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247514 q = 1) (hb : d248602 q = 1) : d249818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247514, d248602, d249818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62513 q ha hb
    | true =>
      simp only [d247514, d248602, d249818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247515 q = 1) (hb : d248603 q = 1) : d249819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247515, d248603, d249819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247515, d248603, d249819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156653 q = 1) (hb : d247410 q = 1) : d249711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62488 q ha hb
    | true =>
      simp only [d156653, d247410, d249711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156654 q = 1) (hb : d247411 q = 1) : d249712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156654, d247411, d249712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247516 q = 1) (hb : d248604 q = 1) : d249820 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247516, d248604, d249820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247516, d248604, d249820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247517 q = 1) (hb : d248605 q = 1) : d249821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247517, d248605, d249821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247517, d248605, d249821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247518 q = 1) (hb : d248606 q = 1) : d249822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247518, d248606, d249822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247518, d248606, d249822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247541 q = 1) (hb : d248614 q = 1) : d249839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247541, d248614, d249839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247541, d248614, d249839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62520 (p : Pattern) (ha : d247550 p = 1) (hb : d248620 p = 1) : d249845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156748 q = 1) (hb : d247493 q = 1) : d249793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156748, d247493, d249793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62507 q ha hb
    | true =>
      simp only [d156748, d247493, d249793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62484 q hb ha
  have h2 (q : Pattern) (ha : d156749 q = 1) (hb : d247494 q = 1) : d249794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156749, d247494, d249794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156749, d247494, d249794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156750 q = 1) (hb : d247495 q = 1) : d249795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156750, d247495, d249795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156750, d247495, d249795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156751 q = 1) (hb : d247496 q = 1) : d249796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156751, d247496, d249796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156751, d247496, d249796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156755 q = 1) (hb : d247500 q = 1) : d249800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156755, d247500, d249800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62508 q ha hb
    | true =>
      simp only [d156755, d247500, d249800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62485 q hb ha
  have h6 (q : Pattern) (ha : d156756 q = 1) (hb : d247501 q = 1) : d249801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156756, d247501, d249801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156756, d247501, d249801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156757 q = 1) (hb : d247502 q = 1) : d249802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156757, d247502, d249802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156757, d247502, d249802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d247520 q = 1) (hb : d248608 q = 1) : d249824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247520, d248608, d249824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62514 q ha hb
    | true =>
      simp only [d247520, d248608, d249824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62489 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247416 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247521 q = 1) (hb : d248609 q = 1) : d249825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247521, d248609, d249825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247521, d248609, d249825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156783 q = 1) (hb : d247526 q = 1) : d249717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156783, d247526, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62509 q ha hb
    | true =>
      simp only [d156783, d247526, d249717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d156784 q = 1) (hb : d247527 q = 1) : d249718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156784, d247527, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156784, d247527, d249718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d247528 q = 1) (hb : d248610 q = 1) : d249826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247528, d248610, d249826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247528, d248610, d249826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d247529 q = 1) (hb : d248611 q = 1) : d249827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247529, d248611, d249827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d247529, d248611, d249827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247530 q = 1) (hb : d248612 q = 1) : d249828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247530, d248612, d249828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d247530, d248612, d249828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156790 q = 1) (hb : d247533 q = 1) : d249831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156790, d247533, d249831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62516 q ha hb
    | true =>
      simp only [d156790, d247533, d249831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62491 q hb ha
  have h17 (q : Pattern) (ha : d156791 q = 1) (hb : d247534 q = 1) : d249832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156791, d247534, d249832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156791, d247534, d249832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156792 q = 1) (hb : d247535 q = 1) : d249833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156792, d247535, d249833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156792, d247535, d249833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d156793 q = 1) (hb : d247536 q = 1) : d249834 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156793, d247536, d249834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156793, d247536, d249834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d156795 q = 1) (hb : d247538 q = 1) : d249836 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156795, d247538, d249836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62517 q ha hb
    | true =>
      simp only [d156795, d247538, d249836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62492 q hb ha
  have h21 (q : Pattern) (ha : d156796 q = 1) (hb : d247539 q = 1) : d249837 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156796, d247539, d249837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156796, d247539, d249837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d156797 q = 1) (hb : d247540 q = 1) : d249838 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156797, d247540, d249838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d156797, d247540, d249838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d247542 q = 1) (hb : d248615 q = 1) : d249840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247542, d248615, d249840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62519 q ha hb
    | true =>
      simp only [d247542, d248615, d249840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d247423 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d247543 q = 1) (hb : d248616 q = 1) : d249841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247543, d248616, d249841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d247543, d248616, d249841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d156802 q = 1) (hb : d247545 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156802, d247545, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62518 q ha hb
    | true =>
      simp only [d156802, d247545, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d156803 q = 1) (hb : d247546 q = 1) : d249725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156803, d247546, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d156803, d247546, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d247547 q = 1) (hb : d248617 q = 1) : d249842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247547, d248617, d249842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d247547, d248617, d249842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d247548 q = 1) (hb : d248618 q = 1) : d249843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247548, d248618, d249843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d247548, d248618, d249843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d247549 q = 1) (hb : d248619 q = 1) : d249844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247549, d248619, d249844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d247549, d248619, d249844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d247550 q = 1) (hb : d248620 q = 1) : d249845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247550, d248620, d249845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247550, d248620, d249845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62521 (p : Pattern) (ha : d247559 p = 1) (hb : d248627 p = 1) : d249854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247542 q = 1) (hb : d248615 q = 1) : d249840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247542, d248615, d249840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62519 q ha hb
    | true =>
      simp only [d247542, d248615, d249840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62493 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247423 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247543 q = 1) (hb : d248616 q = 1) : d249841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247543, d248616, d249841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247543, d248616, d249841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156802 q = 1) (hb : d247545 q = 1) : d249724 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156802, d247545, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62518 q ha hb
    | true =>
      simp only [d156802, d247545, d249724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156803 q = 1) (hb : d247546 q = 1) : d249725 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156803, d247546, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156803, d247546, d249725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d247547 q = 1) (hb : d248617 q = 1) : d249842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247547, d248617, d249842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247547, d248617, d249842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d247557 q = 1) (hb : d248625 q = 1) : d249852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247557, d248625, d249852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247557, d248625, d249852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247558 q = 1) (hb : d248626 q = 1) : d249853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247558, d248626, d249853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247558, d248626, d249853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247559 q = 1) (hb : d248627 q = 1) : d249854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247559, d248627, d249854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247559, d248627, d249854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62522 (p : Pattern) (ha : d156847 p = 1) (hb : d247587 p = 1) : d249757 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156707 q = 1) (hb : d247452 q = 1) : d249752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62497 q ha hb
    | true =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d156708 q = 1) (hb : d247453 q = 1) : d249753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156844 q = 1) (hb : d247584 q = 1) : d249754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156844, d247584, d249754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156844, d247584, d249754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156845 q = 1) (hb : d247585 q = 1) : d249755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156845, d247585, d249755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156845, d247585, d249755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156846 q = 1) (hb : d247586 q = 1) : d249756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156846, d247586, d249756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156846, d247586, d249756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d156847 q = 1) (hb : d247587 q = 1) : d249757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156847, d247587, d249757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156847, d247587, d249757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62523 (p : Pattern) (ha : d247569 p = 1) (hb : d248642 p = 1) : d249865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247565 q = 1) (hb : d248633 q = 1) : d249860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247565, d248633, d249860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247565, d248633, d249860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
  have h2 (q : Pattern) (ha : d247503 q = 1) (hb : d248585 q = 1) : d249806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
    | true =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247566 q = 1) (hb : d248634 q = 1) : d249861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247566, d248634, d249861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247566, d248634, d249861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247504 q = 1) (hb : d248586 q = 1) : d249807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247567 q = 1) (hb : d248635 q = 1) : d249862 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247567, d248635, d249862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247567, d248635, d249862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247568 q = 1) (hb : d248636 q = 1) : d249863 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247568, d248636, d249863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247568, d248636, d249863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247441 q = 1) (hb : d248637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247441, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247441, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62510 q ha hb
  have h8 (q : Pattern) (ha : d247399 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247399, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62510 q ha hb
    | true =>
      simp only [d247399, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247442 q = 1) (hb : d248638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247442, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247442, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247400 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247400, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247400, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d247443 q = 1) (hb : d248639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247443, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247443, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247444 q = 1) (hb : d248640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247444, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247444, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247569 q = 1) (hb : d248641 q = 1) : d249864 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247569, d248641, d249864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247569, d248641, d249864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247569 q = 1) (hb : d248642 q = 1) : d249865 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248642, d249865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248642, d249865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62524 (p : Pattern) (ha : d247575 p = 1) (hb : d248648 p = 1) : d249871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247570 q = 1) (hb : d248643 q = 1) : d249866 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247570, d248643, d249866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62523 q ha hb
    | true =>
      simp only [d247570, d248643, d249866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62496 q hb ha
  have h2 (q : Pattern) (ha : d247571 q = 1) (hb : d248644 q = 1) : d249867 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247571, d248644, d249867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247571, d248644, d249867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247572 q = 1) (hb : d248645 q = 1) : d249868 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247572, d248645, d249868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247572, d248645, d249868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156701 q = 1) (hb : d247446 q = 1) : d249746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156701, d247446, d249746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62496 q ha hb
    | true =>
      simp only [d156701, d247446, d249746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62476 q hb ha
  have h5 (q : Pattern) (ha : d156702 q = 1) (hb : d247447 q = 1) : d249747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156702, d247447, d249747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156702, d247447, d249747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156703 q = 1) (hb : d247448 q = 1) : d249748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156703, d247448, d249748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156703, d247448, d249748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247573 q = 1) (hb : d248646 q = 1) : d249869 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247573, d248646, d249869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247573, d248646, d249869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d118660 q = 1) (hb : d156584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62476 q ha hb
    | true =>
      simp only [d118660, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118661 q = 1) (hb : d156585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118661, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118662 q = 1) (hb : d156586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118662, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156704 q = 1) (hb : d247449 q = 1) : d249749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156704, d247449, d249749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156704, d247449, d249749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d247574 q = 1) (hb : d248647 q = 1) : d249870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247574, d248647, d249870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247574, d248647, d249870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d247575 q = 1) (hb : d248648 q = 1) : d249871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247575, d248648, d249871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d247575, d248648, d249871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62525 (p : Pattern) (ha : d247581 p = 1) (hb : d248654 p = 1) : d249877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247576 q = 1) (hb : d248649 q = 1) : d249872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247576, d248649, d249872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62524 q ha hb
    | true =>
      simp only [d247576, d248649, d249872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247577 q = 1) (hb : d248650 q = 1) : d249873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247577, d248650, d249873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247577, d248650, d249873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156707 q = 1) (hb : d247452 q = 1) : d249752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62497 q ha hb
    | true =>
      simp only [d156707, d247452, d249752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d156708 q = 1) (hb : d247453 q = 1) : d249753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156708, d247453, d249753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247578 q = 1) (hb : d248651 q = 1) : d249874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247578, d248651, d249874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247578, d248651, d249874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d247579 q = 1) (hb : d248652 q = 1) : d249875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247579, d248652, d249875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247579, d248652, d249875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247580 q = 1) (hb : d248653 q = 1) : d249876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247580, d248653, d249876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247580, d248653, d249876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247581 q = 1) (hb : d248654 q = 1) : d249877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247581, d248654, d249877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247581, d248654, d249877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62526 (p : Pattern) (ha : d247593 p = 1) (hb : d248660 p = 1) : d249883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247582 q = 1) (hb : d248655 q = 1) : d249878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247582, d248655, d249878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62525 q ha hb
    | true =>
      simp only [d247582, d248655, d249878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62498 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247583 q = 1) (hb : d248656 q = 1) : d249879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247583, d248656, d249879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247583, d248656, d249879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156848 q = 1) (hb : d247588 q = 1) : d249758 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156848, d247588, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62522 q ha hb
    | true =>
      simp only [d156848, d247588, d249758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156849 q = 1) (hb : d247589 q = 1) : d249759 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156849, d247589, d249759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156849, d247589, d249759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d247590 q = 1) (hb : d248657 q = 1) : d249880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247590, d248657, d249880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247590, d248657, d249880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d247591 q = 1) (hb : d248658 q = 1) : d249881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247591, d248658, d249881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247591, d248658, d249881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247592 q = 1) (hb : d248659 q = 1) : d249882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247592, d248659, d249882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247592, d248659, d249882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247593 q = 1) (hb : d248660 q = 1) : d249883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247593, d248660, d249883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247593, d248660, d249883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62527 (p : Pattern) (ha : d247599 p = 1) (hb : d248666 p = 1) : d249889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156736 q = 1) (hb : d247481 q = 1) : d249781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156736, d247481, d249781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156736, d247481, d249781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62504 q ha hb
  have h2 (q : Pattern) (ha : d156737 q = 1) (hb : d247482 q = 1) : d249782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156737, d247482, d249782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156737, d247482, d249782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d156743 q = 1) (hb : d247488 q = 1) : d249788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156743, d247488, d249788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62504 q ha hb
    | true =>
      simp only [d156743, d247488, d249788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62505 q ha hb
  have h4 (q : Pattern) (ha : d156744 q = 1) (hb : d247489 q = 1) : d249789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156744, d247489, d249789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156744, d247489, d249789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156745 q = 1) (hb : d247490 q = 1) : d249790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156745, d247490, d249790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156745, d247490, d249790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247551 q = 1) (hb : d248621 q = 1) : d249846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247551, d248621, d249846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62515 q ha hb
    | true =>
      simp only [d247551, d248621, d249846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62520 q ha hb
  have h7 (q : Pattern) (ha : d156810 q = 1) (hb : d247553 q = 1) : d249848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156810, d247553, d249848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62506 q ha hb
    | true =>
      simp only [d156810, d247553, d249848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62482 q hb ha
  have h8 (q : Pattern) (ha : d247554 q = 1) (hb : d248622 q = 1) : d249849 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247554, d248622, d249849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247554, d248622, d249849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d247555 q = 1) (hb : d248623 q = 1) : d249850 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247555, d248623, d249850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247555, d248623, d249850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d247556 q = 1) (hb : d248624 q = 1) : d249851 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247556, d248624, d249851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d247556, d248624, d249851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247560 q = 1) (hb : d248628 q = 1) : d249855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247560, d248628, d249855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247560, d248628, d249855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62521 q ha hb
  have h12 (q : Pattern) (ha : d118890 q = 1) (hb : d156819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118890, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118890, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62502 q ha hb
  have h13 (q : Pattern) (ha : d247561 q = 1) (hb : d248629 q = 1) : d249856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247561, d248629, d249856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247561, d248629, d249856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247562 q = 1) (hb : d248630 q = 1) : d249857 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247562, d248630, d249857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247562, d248630, d249857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d247563 q = 1) (hb : d248631 q = 1) : d249858 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247563, d248631, d249858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d247563, d248631, d249858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d247564 q = 1) (hb : d248632 q = 1) : d249859 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247564, d248632, d249859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247564, d248632, d249859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d247594 q = 1) (hb : d248661 q = 1) : d249884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247594, d248661, d249884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247594, d248661, d249884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62526 q ha hb
  have h18 (q : Pattern) (ha : d118930 q = 1) (hb : d156860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118930, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118930, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62503 q ha hb
  have h19 (q : Pattern) (ha : d247595 q = 1) (hb : d248662 q = 1) : d249885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247595, d248662, d249885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d247595, d248662, d249885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d247596 q = 1) (hb : d248663 q = 1) : d249886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247596, d248663, d249886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d247596, d248663, d249886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d247597 q = 1) (hb : d248664 q = 1) : d249887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247597, d248664, d249887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d247597, d248664, d249887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d247598 q = 1) (hb : d248665 q = 1) : d249888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247598, d248665, d249888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d247598, d248665, d249888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d247599 q = 1) (hb : d248666 q = 1) : d249889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d247599, d248666, d249889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d247599, d248666, d249889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62528 (p : Pattern) (ha : d247605 p = 1) (hb : d248672 p = 1) : d249895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247600 q = 1) (hb : d248667 q = 1) : d249890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d247600, d248667, d249890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247600, d248667, d249890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62527 q ha hb
  have h2 (q : Pattern) (ha : d247601 q = 1) (hb : d248668 q = 1) : d249891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d247601, d248668, d249891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247601, d248668, d249891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247602 q = 1) (hb : d248669 q = 1) : d249892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d247602, d248669, d249892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247602, d248669, d249892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247603 q = 1) (hb : d248670 q = 1) : d249893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d247603, d248670, d249893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247603, d248670, d249893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247604 q = 1) (hb : d248671 q = 1) : d249894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d247604, d248671, d249894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247604, d248671, d249894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247605 q = 1) (hb : d248672 q = 1) : d249895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d247605, d248672, d249895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247605, d248672, d249895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62529 (p : Pattern) (ha : d51988 p = 1) (hb : d156640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d25102 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25102, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25103 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25103, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d51988 q = 1) (hb : d156640 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62530 (p : Pattern) (ha : d118943 p = 1) (hb : d156874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118716 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62529 q ha hb
    | true =>
      simp only [d118716, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118717 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118717, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118718 q = 1) (hb : d156643 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118718, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118718, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118719 q = 1) (hb : d156644 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118719, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118719, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118943 q = 1) (hb : d156873 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118943, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118943, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118943 q = 1) (hb : d156874 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62531 (p : Pattern) (ha : d118957 p = 1) (hb : d156888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118947 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62530 q ha hb
    | true =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118948 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118949 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118951 q = 1) (hb : d156882 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118951, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118951, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118956 q = 1) (hb : d156887 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118956, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118956, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118957 q = 1) (hb : d156888 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118957, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118957, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62532 (p : Pattern) (ha : d118967 p = 1) (hb : d156898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118966 q = 1) (hb : d156897 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118966, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118966, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118967 q = 1) (hb : d156898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118967, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118967, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62533 (p : Pattern) (ha : d118977 p = 1) (hb : d156908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118966 q = 1) (hb : d156897 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118966, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118966, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118977 q = 1) (hb : d156908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118977, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118977, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62534 (p : Pattern) (ha : d119074 p = 1) (hb : d157011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119063 q = 1) (hb : d157000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119063, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
    | true =>
      simp only [d119063, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119064 q = 1) (hb : d157001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119064, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119064, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119065 q = 1) (hb : d157002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119065, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119065, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119066 q = 1) (hb : d157003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119066, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119066, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119067 q = 1) (hb : d157004 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119067, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119067, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119069 q = 1) (hb : d157006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119069, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62533 q ha hb
    | true =>
      simp only [d119069, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119070 q = 1) (hb : d157007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119070, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119070, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119071 q = 1) (hb : d157008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119071, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119071, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119072 q = 1) (hb : d157009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119072, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119072, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119073 q = 1) (hb : d157010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119073, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119073, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119074 q = 1) (hb : d157011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119074, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119074, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62535 (p : Pattern) (ha : d119083 p = 1) (hb : d157020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119069 q = 1) (hb : d157006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119069, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62533 q ha hb
    | true =>
      simp only [d119069, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119070 q = 1) (hb : d157007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119070, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119070, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119071 q = 1) (hb : d157008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119071, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119071, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119072 q = 1) (hb : d157009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119072, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119072, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119073 q = 1) (hb : d157010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119073, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119073, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119083 q = 1) (hb : d157020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119083, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119083, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62536 (p : Pattern) (ha : d119106 p = 1) (hb : d157046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118769 q = 1) (hb : d156695 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118769, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118769, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62529 q ha hb
  have h2 (q : Pattern) (ha : d118716 q = 1) (hb : d156641 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62529 q ha hb
    | true =>
      simp only [d118716, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118770 q = 1) (hb : d156696 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118770, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118770, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118717 q = 1) (hb : d156642 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118717, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118771 q = 1) (hb : d156697 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118771, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118771, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118772 q = 1) (hb : d156698 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118772, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118772, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119106 q = 1) (hb : d157045 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d119106, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119106, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119106 q = 1) (hb : d157046 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62537 (p : Pattern) (ha : d119128 p = 1) (hb : d157068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119110 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62536 q ha hb
    | true =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119111 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119112 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119118 q = 1) (hb : d157058 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119118, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119118, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119127 q = 1) (hb : d157067 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d119127, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119127, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119128 q = 1) (hb : d157068 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d119128, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119128, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62538 (p : Pattern) (ha : d119139 p = 1) (hb : d157091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119129 q = 1) (hb : d157069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119129, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62537 q ha hb
    | true =>
      simp only [d119129, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119130 q = 1) (hb : d157070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119130, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119130, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119136 q = 1) (hb : d157088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d119136, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119136, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119137 q = 1) (hb : d157089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d119137, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119137, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119138 q = 1) (hb : d157090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d119138, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d119138, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119139 q = 1) (hb : d157091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119139, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119139, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62539 (p : Pattern) (ha : d119158 p = 1) (hb : d157097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d119153 q = 1) (hb : d157092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119153, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62538 q ha hb
    | true =>
      simp only [d119153, d157092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d119154 q = 1) (hb : d157093 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119154, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119154, d157093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119155 q = 1) (hb : d157094 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119155, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119155, d157094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119156 q = 1) (hb : d157095 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119156, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119156, d157095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d119157 q = 1) (hb : d157096 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119157, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119157, d157096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119158 q = 1) (hb : d157097 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d119158, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119158, d157097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62540 (p : Pattern) (ha : d51988 p = 1) (hb : d248589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9796 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9796, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25219 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25219, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25220 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25220, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d51988 q = 1) (hb : d248589 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62541 (p : Pattern) (ha : d247607 p = 1) (hb : d248595 p = 1) : d249811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247503 q = 1) (hb : d248585 q = 1) : d249806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
    | true =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247504 q = 1) (hb : d248586 q = 1) : d249807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247505 q = 1) (hb : d248587 q = 1) : d249808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247505, d248587, d249808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247505, d248587, d249808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247506 q = 1) (hb : d248588 q = 1) : d249809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247506, d248588, d249809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247506, d248588, d249809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118716 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
    | true =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d118717 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118718 q = 1) (hb : d248592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118718, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118718, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118719 q = 1) (hb : d248593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118719, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118719, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247607 q = 1) (hb : d248594 q = 1) : d249810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247607, d248594, d249810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247607, d248594, d249810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247607 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d247607 q = 1) (hb : d248595 q = 1) : d249811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248595, d249811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248595, d249811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62542 (p : Pattern) (ha : d247613 p = 1) (hb : d248679 p = 1) : d249902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247608 q = 1) (hb : d248674 q = 1) : d249897 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247608, d248674, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62541 q ha hb
    | true =>
      simp only [d247608, d248674, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62530 q ha hb
  have h2 (q : Pattern) (ha : d247609 q = 1) (hb : d248675 q = 1) : d249898 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247609, d248675, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247609, d248675, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247610 q = 1) (hb : d248676 q = 1) : d249899 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247610, d248676, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247610, d248676, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118947 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62530 q ha hb
    | true =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118948 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118949 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247611 q = 1) (hb : d248677 q = 1) : d249900 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247611, d248677, d249900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247611, d248677, d249900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d118951 q = 1) (hb : d156882 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118951, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d118951, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247612 q = 1) (hb : d248678 q = 1) : d249901 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247612, d248678, d249901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247612, d248678, d249901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247613 q = 1) (hb : d248679 q = 1) : d249902 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247613, d248679, d249902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247613, d248679, d249902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62543 (p : Pattern) (ha : d247619 p = 1) (hb : d248685 p = 1) : d249908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247617 q = 1) (hb : d248683 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247618 q = 1) (hb : d248684 q = 1) : d249907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247618, d248684, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247618, d248684, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247619 q = 1) (hb : d248685 q = 1) : d249908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247619, d248685, d249908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247619, d248685, d249908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62544 (p : Pattern) (ha : d247625 p = 1) (hb : d248691 p = 1) : d249914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247620 q = 1) (hb : d248686 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
    | true =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
  have h2 (q : Pattern) (ha : d247621 q = 1) (hb : d248687 q = 1) : d249910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247622 q = 1) (hb : d248688 q = 1) : d249911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247623 q = 1) (hb : d248689 q = 1) : d249912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247624 q = 1) (hb : d248690 q = 1) : d249913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247625 q = 1) (hb : d248691 q = 1) : d249914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247625, d248691, d249914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247625, d248691, d249914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62545 (p : Pattern) (ha : d247628 p = 1) (hb : d248694 p = 1) : d249917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247617 q = 1) (hb : d248683 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247618 q = 1) (hb : d248684 q = 1) : d249907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247618, d248684, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247618, d248684, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247628 q = 1) (hb : d248694 q = 1) : d249917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247628, d248694, d249917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247628, d248694, d249917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62546 (p : Pattern) (ha : d247634 p = 1) (hb : d248700 p = 1) : d249923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247620 q = 1) (hb : d248686 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
    | true =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
  have h2 (q : Pattern) (ha : d247621 q = 1) (hb : d248687 q = 1) : d249910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247622 q = 1) (hb : d248688 q = 1) : d249911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247623 q = 1) (hb : d248689 q = 1) : d249912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247624 q = 1) (hb : d248690 q = 1) : d249913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247629 q = 1) (hb : d248695 q = 1) : d249918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62545 q ha hb
    | true =>
      simp only [d247629, d248695, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62533 q ha hb
  have h7 (q : Pattern) (ha : d247630 q = 1) (hb : d248696 q = 1) : d249919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247630, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247630, d248696, d249919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247631 q = 1) (hb : d248697 q = 1) : d249920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247631, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247631, d248697, d249920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247632 q = 1) (hb : d248698 q = 1) : d249921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247632, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247632, d248698, d249921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247633 q = 1) (hb : d248699 q = 1) : d249922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247633, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247633, d248699, d249922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247634 q = 1) (hb : d248700 q = 1) : d249923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247634, d248700, d249923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247634, d248700, d249923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62547 (p : Pattern) (ha : d118990 p = 1) (hb : d156921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118989 q = 1) (hb : d156920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118989, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118989, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118990 q = 1) (hb : d156921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118990, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118990, d156921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62548 (p : Pattern) (ha : d119000 p = 1) (hb : d156931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118998 q = 1) (hb : d156929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118998, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118998, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118999 q = 1) (hb : d156930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118999, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118999, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119000 q = 1) (hb : d156931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119000, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119000, d156931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62549 (p : Pattern) (ha : d247639 p = 1) (hb : d248705 p = 1) : d249928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247617 q = 1) (hb : d248683 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247638 q = 1) (hb : d248704 q = 1) : d249927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247638, d248704, d249927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247638, d248704, d249927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247639 q = 1) (hb : d248705 q = 1) : d249928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247639, d248705, d249928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247639, d248705, d249928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62550 (p : Pattern) (ha : d247646 p = 1) (hb : d248712 p = 1) : d249935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247644 q = 1) (hb : d248710 q = 1) : d249933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247644, d248710, d249933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247644, d248710, d249933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247645 q = 1) (hb : d248711 q = 1) : d249934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247645, d248711, d249934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247645, d248711, d249934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247646 q = 1) (hb : d248712 q = 1) : d249935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247646, d248712, d249935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247646, d248712, d249935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62551 (p : Pattern) (ha : d118943 p = 1) (hb : d248732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118716 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
    | true =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118717 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118718 q = 1) (hb : d248592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118718, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118718, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118719 q = 1) (hb : d248593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118719, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118719, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118943 q = 1) (hb : d248731 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118943, d248731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118943, d248731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d118943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d118943 q = 1) (hb : d248732 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62552 (p : Pattern) (ha : d101081 p = 1) (hb : d248721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101081 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25210 q = 1) (hb : d101079 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25210, d101079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25449 q = 1) (hb : d101080 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d101080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25449, d101080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d25450 q = 1) (hb : d101081 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d101081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25450, d101081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d101081 q = 1) (hb : d248721 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62553 (p : Pattern) (ha : d101175 p = 1) (hb : d248716 p = 1) : d249941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d531 q = 1) (hb : d52278 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25428 q = 1) (hb : d101173 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d101173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25428, d101173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d25767 q = 1) : d25767 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d25768 q = 1) (hb : d101174 q = 1) : d249939 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25768, d101174, d249939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25768, d101174, d249939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25769 q = 1) (hb : d101175 q = 1) : d249940 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25769, d101175, d249940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25769, d101175, d249940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d101175 q = 1) (hb : d248716 q = 1) : d249941 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248716, d249941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248716, d249941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62554 (p : Pattern) (ha : d247654 p = 1) (hb : d248727 p = 1) : d249947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247650 q = 1) (hb : d248717 q = 1) : d249942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247650, d248717, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62553 q ha hb
    | true =>
      simp only [d247650, d248717, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247651 q = 1) (hb : d248718 q = 1) : d249943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247651, d248718, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247651, d248718, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247652 q = 1) (hb : d248719 q = 1) : d249944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247652, d248719, d249944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247652, d248719, d249944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247653 q = 1) (hb : d248720 q = 1) : d249945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247653, d248720, d249945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247653, d248720, d249945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247503 q = 1) (hb : d248722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62552 q ha hb
    | true =>
      simp only [d247503, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247504 q = 1) (hb : d248723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247504, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247505 q = 1) (hb : d248724 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247505, d248724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247505, d248724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247506 q = 1) (hb : d248725 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247506, d248725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247506, d248725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247654 q = 1) (hb : d248726 q = 1) : d249946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247654, d248726, d249946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247654, d248726, d249946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247654 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d247654 q = 1) (hb : d248727 q = 1) : d249947 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248727, d249947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248727, d249947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62555 (p : Pattern) (ha : d247660 p = 1) (hb : d248738 p = 1) : d249953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247655 q = 1) (hb : d248728 q = 1) : d249948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247655, d248728, d249948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62554 q ha hb
    | true =>
      simp only [d247655, d248728, d249948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62541 q ha hb
  have h2 (q : Pattern) (ha : d247656 q = 1) (hb : d248729 q = 1) : d249949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247656, d248729, d249949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247656, d248729, d249949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247657 q = 1) (hb : d248730 q = 1) : d249950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247657, d248730, d249950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247657, d248730, d249950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247608 q = 1) (hb : d248733 q = 1) : d249897 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247608, d248733, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62541 q ha hb
    | true =>
      simp only [d247608, d248733, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62551 q ha hb
  have h5 (q : Pattern) (ha : d247609 q = 1) (hb : d248734 q = 1) : d249898 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247609, d248734, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247609, d248734, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247610 q = 1) (hb : d248735 q = 1) : d249899 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247610, d248735, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247610, d248735, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247658 q = 1) (hb : d248736 q = 1) : d249951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247658, d248736, d249951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247658, d248736, d249951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247608 q = 1) (hb : d248674 q = 1) : d249897 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247608, d248674, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62541 q ha hb
    | true =>
      simp only [d247608, d248674, d249897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62530 q ha hb
  have h9 (q : Pattern) (ha : d247609 q = 1) (hb : d248675 q = 1) : d249898 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247609, d248675, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247609, d248675, d249898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247610 q = 1) (hb : d248676 q = 1) : d249899 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247610, d248676, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247610, d248676, d249899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d118947 q = 1) (hb : d156878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62530 q ha hb
    | true =>
      simp only [d118947, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d118948 q = 1) (hb : d156879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118948, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d118949 q = 1) (hb : d156880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118949, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247611 q = 1) (hb : d248677 q = 1) : d249900 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247611, d248677, d249900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247611, d248677, d249900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247659 q = 1) (hb : d248737 q = 1) : d249952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247659, d248737, d249952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247659, d248737, d249952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247660 q = 1) (hb : d248738 q = 1) : d249953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247660, d248738, d249953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247660, d248738, d249953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62556 (p : Pattern) (ha : d247666 p = 1) (hb : d248744 p = 1) : d249959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247661 q = 1) (hb : d248739 q = 1) : d249954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247661, d248739, d249954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62555 q ha hb
    | true =>
      simp only [d247661, d248739, d249954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247662 q = 1) (hb : d248740 q = 1) : d249955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247662, d248740, d249955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247662, d248740, d249955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247663 q = 1) (hb : d248741 q = 1) : d249956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247663, d248741, d249956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247663, d248741, d249956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247664 q = 1) (hb : d248742 q = 1) : d249957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247664, d248742, d249957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247664, d248742, d249957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247665 q = 1) (hb : d248743 q = 1) : d249958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247665, d248743, d249958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247665, d248743, d249958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247666 q = 1) (hb : d248744 q = 1) : d249959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247666, d248744, d249959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247666, d248744, d249959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62557 (p : Pattern) (ha : d247672 p = 1) (hb : d248750 p = 1) : d249908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247669 q = 1) (hb : d248747 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247669, d248747, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247669, d248747, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247670 q = 1) (hb : d248748 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247670, d248748, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247670, d248748, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247671 q = 1) (hb : d248749 q = 1) : d249907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247671, d248749, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247671, d248749, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247672 q = 1) (hb : d248750 q = 1) : d249908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247672, d248750, d249908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247672, d248750, d249908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62558 (p : Pattern) (ha : d247678 p = 1) (hb : d248756 p = 1) : d249966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247640 q = 1) (hb : d248706 q = 1) : d249929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247640, d248706, d249929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62549 q ha hb
    | true =>
      simp only [d247640, d248706, d249929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62547 q ha hb
  have h2 (q : Pattern) (ha : d247641 q = 1) (hb : d248707 q = 1) : d249930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247641, d248707, d249930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247641, d248707, d249930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247642 q = 1) (hb : d248708 q = 1) : d249931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247642, d248708, d249931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247642, d248708, d249931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247643 q = 1) (hb : d248709 q = 1) : d249932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247643, d248709, d249932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247643, d248709, d249932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247647 q = 1) (hb : d248713 q = 1) : d249936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247647, d248713, d249936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62550 q ha hb
    | true =>
      simp only [d247647, d248713, d249936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62548 q ha hb
  have h6 (q : Pattern) (ha : d247648 q = 1) (hb : d248714 q = 1) : d249937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247648, d248714, d249937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247648, d248714, d249937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247649 q = 1) (hb : d248715 q = 1) : d249938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247649, d248715, d249938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247649, d248715, d249938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247667 q = 1) (hb : d248745 q = 1) : d249960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247667, d248745, d249960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62556 q ha hb
    | true =>
      simp only [d247667, d248745, d249960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247620 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247668 q = 1) (hb : d248746 q = 1) : d249961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247668, d248746, d249961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247668, d248746, d249961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d247673 q = 1) (hb : d248751 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247673, d248751, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62557 q ha hb
    | true =>
      simp only [d247673, d248751, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d247674 q = 1) (hb : d248752 q = 1) : d249962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247674, d248752, d249962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247674, d248752, d249962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247675 q = 1) (hb : d248753 q = 1) : d249963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247675, d248753, d249963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247675, d248753, d249963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247676 q = 1) (hb : d248754 q = 1) : d249964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247676, d248754, d249964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247676, d248754, d249964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247677 q = 1) (hb : d248755 q = 1) : d249965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247677, d248755, d249965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247677, d248755, d249965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247678 q = 1) (hb : d248756 q = 1) : d249966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247678, d248756, d249966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247678, d248756, d249966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62559 (p : Pattern) (ha : d119042 p = 1) (hb : d156979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118965 q = 1) (hb : d156896 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118965, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118989 q = 1) (hb : d156920 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118989, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118989, d156920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119042 q = 1) (hb : d156979 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119042, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119042, d156979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62560 (p : Pattern) (ha : d119048 p = 1) (hb : d156985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118964 q = 1) (hb : d156895 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118964, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118998 q = 1) (hb : d156929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118998, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118998, d156929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d118999 q = 1) (hb : d156930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118999, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d118999, d156930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d119048 q = 1) (hb : d156985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d119048, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d119048, d156985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62561 (p : Pattern) (ha : d247679 p = 1) (hb : d248757 p = 1) : d249967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247617 q = 1) (hb : d248683 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247617, d248683, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247638 q = 1) (hb : d248704 q = 1) : d249927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247638, d248704, d249927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247638, d248704, d249927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247679 q = 1) (hb : d248757 q = 1) : d249967 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247679, d248757, d249967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247679, d248757, d249967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62562 (p : Pattern) (ha : d247684 p = 1) (hb : d248762 p = 1) : d249972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118958 q = 1) (hb : d156889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62531 q ha hb
    | true =>
      simp only [d118958, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d118959 q = 1) (hb : d156890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118959, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247616 q = 1) (hb : d248682 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247616, d248682, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247644 q = 1) (hb : d248710 q = 1) : d249933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247644, d248710, d249933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247644, d248710, d249933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247645 q = 1) (hb : d248711 q = 1) : d249934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247645, d248711, d249934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247645, d248711, d249934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247684 q = 1) (hb : d248762 q = 1) : d249972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247684, d248762, d249972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247684, d248762, d249972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62563 (p : Pattern) (ha : d247688 p = 1) (hb : d248766 p = 1) : d249976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247661 q = 1) (hb : d248739 q = 1) : d249954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247661, d248739, d249954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62555 q ha hb
    | true =>
      simp only [d247661, d248739, d249954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247662 q = 1) (hb : d248740 q = 1) : d249955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247662, d248740, d249955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247662, d248740, d249955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247663 q = 1) (hb : d248741 q = 1) : d249956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247663, d248741, d249956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247663, d248741, d249956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247664 q = 1) (hb : d248742 q = 1) : d249957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247664, d248742, d249957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247664, d248742, d249957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247665 q = 1) (hb : d248743 q = 1) : d249958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247665, d248743, d249958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247665, d248743, d249958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247688 q = 1) (hb : d248766 q = 1) : d249976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247688, d248766, d249976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247688, d248766, d249976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62564 (p : Pattern) (ha : d247691 p = 1) (hb : d248769 p = 1) : d249917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247614 q = 1) (hb : d248680 q = 1) : d249903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62542 q ha hb
    | true =>
      simp only [d247614, d248680, d249903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247615 q = 1) (hb : d248681 q = 1) : d249904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247615, d248681, d249904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247669 q = 1) (hb : d248747 q = 1) : d249905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247669, d248747, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247669, d248747, d249905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247670 q = 1) (hb : d248748 q = 1) : d249906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247670, d248748, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247670, d248748, d249906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247671 q = 1) (hb : d248749 q = 1) : d249907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247671, d248749, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247671, d248749, d249907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247691 q = 1) (hb : d248769 q = 1) : d249917 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247691, d248769, d249917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247691, d248769, d249917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62565 (p : Pattern) (ha : d247697 p = 1) (hb : d248775 p = 1) : d249983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247640 q = 1) (hb : d248706 q = 1) : d249929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247640, d248706, d249929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62549 q ha hb
    | true =>
      simp only [d247640, d248706, d249929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62547 q ha hb
  have h2 (q : Pattern) (ha : d247641 q = 1) (hb : d248707 q = 1) : d249930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247641, d248707, d249930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247641, d248707, d249930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247642 q = 1) (hb : d248708 q = 1) : d249931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247642, d248708, d249931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247642, d248708, d249931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247643 q = 1) (hb : d248709 q = 1) : d249932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247643, d248709, d249932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247643, d248709, d249932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247647 q = 1) (hb : d248713 q = 1) : d249936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247647, d248713, d249936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62550 q ha hb
    | true =>
      simp only [d247647, d248713, d249936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62548 q ha hb
  have h6 (q : Pattern) (ha : d247648 q = 1) (hb : d248714 q = 1) : d249937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247648, d248714, d249937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247648, d248714, d249937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247649 q = 1) (hb : d248715 q = 1) : d249938 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247649, d248715, d249938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247649, d248715, d249938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247667 q = 1) (hb : d248745 q = 1) : d249960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247667, d248745, d249960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62556 q ha hb
    | true =>
      simp only [d247667, d248745, d249960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247620 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247668 q = 1) (hb : d248746 q = 1) : d249961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247668, d248746, d249961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247668, d248746, d249961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d247673 q = 1) (hb : d248751 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247673, d248751, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62557 q ha hb
    | true =>
      simp only [d247673, d248751, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d247674 q = 1) (hb : d248752 q = 1) : d249962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247674, d248752, d249962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247674, d248752, d249962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247675 q = 1) (hb : d248753 q = 1) : d249963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247675, d248753, d249963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247675, d248753, d249963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247676 q = 1) (hb : d248754 q = 1) : d249964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247676, d248754, d249964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247676, d248754, d249964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247677 q = 1) (hb : d248755 q = 1) : d249965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247677, d248755, d249965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247677, d248755, d249965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247680 q = 1) (hb : d248758 q = 1) : d249968 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247680, d248758, d249968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62561 q ha hb
    | true =>
      simp only [d247680, d248758, d249968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62559 q ha hb
  have h17 (q : Pattern) (ha : d247681 q = 1) (hb : d248759 q = 1) : d249969 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247681, d248759, d249969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247681, d248759, d249969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d247682 q = 1) (hb : d248760 q = 1) : d249970 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247682, d248760, d249970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d247682, d248760, d249970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d247683 q = 1) (hb : d248761 q = 1) : d249971 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247683, d248761, d249971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247683, d248761, d249971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d247685 q = 1) (hb : d248763 q = 1) : d249973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247685, d248763, d249973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62562 q ha hb
    | true =>
      simp only [d247685, d248763, d249973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62560 q ha hb
  have h21 (q : Pattern) (ha : d247686 q = 1) (hb : d248764 q = 1) : d249974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247686, d248764, d249974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247686, d248764, d249974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d247687 q = 1) (hb : d248765 q = 1) : d249975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247687, d248765, d249975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d247687, d248765, d249975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d247689 q = 1) (hb : d248767 q = 1) : d249977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247689, d248767, d249977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62563 q ha hb
    | true =>
      simp only [d247689, d248767, d249977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62545 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d247629 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d247690 q = 1) (hb : d248768 q = 1) : d249978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247690, d248768, d249978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d247690, d248768, d249978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d247692 q = 1) (hb : d248770 q = 1) : d249918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247692, d248770, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62564 q ha hb
    | true =>
      simp only [d247692, d248770, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d247693 q = 1) (hb : d248771 q = 1) : d249979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247693, d248771, d249979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d247693, d248771, d249979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d247694 q = 1) (hb : d248772 q = 1) : d249980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247694, d248772, d249980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d247694, d248772, d249980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d247695 q = 1) (hb : d248773 q = 1) : d249981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247695, d248773, d249981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d247695, d248773, d249981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d247696 q = 1) (hb : d248774 q = 1) : d249982 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247696, d248774, d249982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d247696, d248774, d249982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d247697 q = 1) (hb : d248775 q = 1) : d249983 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247697, d248775, d249983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247697, d248775, d249983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62566 (p : Pattern) (ha : d247699 p = 1) (hb : d248777 p = 1) : d249985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247620 q = 1) (hb : d248686 q = 1) : d249909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62543 q ha hb
    | true =>
      simp only [d247620, d248686, d249909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
  have h2 (q : Pattern) (ha : d247621 q = 1) (hb : d248687 q = 1) : d249910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247621, d248687, d249910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247622 q = 1) (hb : d248688 q = 1) : d249911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247622, d248688, d249911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247623 q = 1) (hb : d248689 q = 1) : d249912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247623, d248689, d249912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247624 q = 1) (hb : d248690 q = 1) : d249913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247624, d248690, d249913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119063 q = 1) (hb : d157000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d119063, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62532 q ha hb
    | true =>
      simp only [d119063, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119064 q = 1) (hb : d157001 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d119064, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119064, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119065 q = 1) (hb : d157002 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119065, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d119065, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d119066 q = 1) (hb : d157003 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d119066, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119066, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d119067 q = 1) (hb : d157004 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d119067, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119067, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247699 q = 1) (hb : d248777 q = 1) : d249985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247699, d248777, d249985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247699, d248777, d249985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62567 (p : Pattern) (ha : d247706 p = 1) (hb : d248784 p = 1) : d249992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247689 q = 1) (hb : d248767 q = 1) : d249977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247689, d248767, d249977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62563 q ha hb
    | true =>
      simp only [d247689, d248767, d249977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62545 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247629 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247690 q = 1) (hb : d248768 q = 1) : d249978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247690, d248768, d249978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247690, d248768, d249978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d247692 q = 1) (hb : d248770 q = 1) : d249918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247692, d248770, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62564 q ha hb
    | true =>
      simp only [d247692, d248770, d249918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247693 q = 1) (hb : d248771 q = 1) : d249979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247693, d248771, d249979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247693, d248771, d249979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247694 q = 1) (hb : d248772 q = 1) : d249980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247694, d248772, d249980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247694, d248772, d249980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247704 q = 1) (hb : d248782 q = 1) : d249990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247704, d248782, d249990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247704, d248782, d249990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247705 q = 1) (hb : d248783 q = 1) : d249991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247705, d248783, d249991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247705, d248783, d249991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247706 q = 1) (hb : d248784 q = 1) : d249992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247706, d248784, d249992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247706, d248784, d249992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62568 (p : Pattern) (ha : d119106 p = 1) (hb : d248804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d118769 q = 1) (hb : d248637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118769, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118769, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
  have h2 (q : Pattern) (ha : d118716 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
    | true =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d118770 q = 1) (hb : d248638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118770, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118770, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d118717 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d118771 q = 1) (hb : d248639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118771, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d118771, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d118772 q = 1) (hb : d248640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118772, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d118772, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d119106 q = 1) (hb : d248803 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d119106, d248803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119106, d248803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d119106 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d119106 q = 1) (hb : d248804 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62569 (p : Pattern) (ha : d247716 p = 1) (hb : d248799 p = 1) : d250003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247712 q = 1) (hb : d248790 q = 1) : d249998 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247712, d248790, d249998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247712, d248790, d249998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62553 q ha hb
  have h2 (q : Pattern) (ha : d247650 q = 1) (hb : d248717 q = 1) : d249942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247650, d248717, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62553 q ha hb
    | true =>
      simp only [d247650, d248717, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247713 q = 1) (hb : d248791 q = 1) : d249999 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247713, d248791, d249999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247713, d248791, d249999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247651 q = 1) (hb : d248718 q = 1) : d249943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247651, d248718, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247651, d248718, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247714 q = 1) (hb : d248792 q = 1) : d250000 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247714, d248792, d250000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247714, d248792, d250000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247715 q = 1) (hb : d248793 q = 1) : d250001 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247715, d248793, d250001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247715, d248793, d250001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247565 q = 1) (hb : d248794 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247565, d248794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247565, d248794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62552 q ha hb
  have h8 (q : Pattern) (ha : d247503 q = 1) (hb : d248722 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62552 q ha hb
    | true =>
      simp only [d247503, d248722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247566 q = 1) (hb : d248795 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247566, d248795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247566, d248795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247504 q = 1) (hb : d248723 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247504, d248723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d247567 q = 1) (hb : d248796 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247567, d248796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247567, d248796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247568 q = 1) (hb : d248797 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247568, d248797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247568, d248797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247716 q = 1) (hb : d248798 q = 1) : d250002 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247716, d248798, d250002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247716, d248798, d250002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247716 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247716 q = 1) (hb : d248799 q = 1) : d250003 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248799, d250003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248799, d250003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62570 (p : Pattern) (ha : d247717 p = 1) (hb : d248642 p = 1) : d249865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247565 q = 1) (hb : d248633 q = 1) : d249860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247565, d248633, d249860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247565, d248633, d249860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
  have h2 (q : Pattern) (ha : d247503 q = 1) (hb : d248585 q = 1) : d249806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62511 q ha hb
    | true =>
      simp only [d247503, d248585, d249806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247566 q = 1) (hb : d248634 q = 1) : d249861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247566, d248634, d249861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247566, d248634, d249861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247504 q = 1) (hb : d248586 q = 1) : d249807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247504, d248586, d249807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247567 q = 1) (hb : d248635 q = 1) : d249862 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247567, d248635, d249862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247567, d248635, d249862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247568 q = 1) (hb : d248636 q = 1) : d249863 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247568, d248636, d249863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247568, d248636, d249863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d118769 q = 1) (hb : d248637 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118769, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d118769, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
  have h8 (q : Pattern) (ha : d118716 q = 1) (hb : d248590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62540 q ha hb
    | true =>
      simp only [d118716, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d118770 q = 1) (hb : d248638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118770, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d118770, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d118717 q = 1) (hb : d248591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d118717, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d118771 q = 1) (hb : d248639 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118771, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d118771, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d118772 q = 1) (hb : d248640 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118772, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d118772, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247717 q = 1) (hb : d248641 q = 1) : d249864 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247717, d248641, d249864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247717, d248641, d249864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247717 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247717 q = 1) (hb : d248642 q = 1) : d249865 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248642, d249865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248642, d249865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62571 (p : Pattern) (ha : d247727 p = 1) (hb : d248814 p = 1) : d250013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247718 q = 1) (hb : d248800 q = 1) : d250004 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247718, d248800, d250004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62569 q ha hb
    | true =>
      simp only [d247718, d248800, d250004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62570 q ha hb
  have h2 (q : Pattern) (ha : d247719 q = 1) (hb : d248801 q = 1) : d250005 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247719, d248801, d250005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247719, d248801, d250005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247720 q = 1) (hb : d248802 q = 1) : d250006 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247720, d248802, d250006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247720, d248802, d250006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247721 q = 1) (hb : d248805 q = 1) : d250007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247721, d248805, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62570 q ha hb
    | true =>
      simp only [d247721, d248805, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62568 q ha hb
  have h5 (q : Pattern) (ha : d247722 q = 1) (hb : d248806 q = 1) : d250008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247722, d248806, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247722, d248806, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247723 q = 1) (hb : d248807 q = 1) : d250009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247723, d248807, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247723, d248807, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247724 q = 1) (hb : d248808 q = 1) : d250010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247724, d248808, d250010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247724, d248808, d250010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247721 q = 1) (hb : d248809 q = 1) : d250007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247721, d248809, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62570 q ha hb
    | true =>
      simp only [d247721, d248809, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62536 q ha hb
  have h9 (q : Pattern) (ha : d247722 q = 1) (hb : d248810 q = 1) : d250008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247722, d248810, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247722, d248810, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247723 q = 1) (hb : d248811 q = 1) : d250009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247723, d248811, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247723, d248811, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d119110 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62536 q ha hb
    | true =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d119111 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d119112 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247725 q = 1) (hb : d248812 q = 1) : d250011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247725, d248812, d250011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247725, d248812, d250011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247726 q = 1) (hb : d248813 q = 1) : d250012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247726, d248813, d250012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247726, d248813, d250012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247727 q = 1) (hb : d248814 q = 1) : d250013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247727, d248814, d250013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247727, d248814, d250013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62572 (p : Pattern) (ha : d247731 p = 1) (hb : d248818 p = 1) : d250017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247721 q = 1) (hb : d248809 q = 1) : d250007 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247721, d248809, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62570 q ha hb
    | true =>
      simp only [d247721, d248809, d250007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62536 q ha hb
  have h2 (q : Pattern) (ha : d247722 q = 1) (hb : d248810 q = 1) : d250008 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247722, d248810, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247722, d248810, d250008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247723 q = 1) (hb : d248811 q = 1) : d250009 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247723, d248811, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247723, d248811, d250009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119110 q = 1) (hb : d157050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62536 q ha hb
    | true =>
      simp only [d119110, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d119111 q = 1) (hb : d157051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119111, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d119112 q = 1) (hb : d157052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119112, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247725 q = 1) (hb : d248812 q = 1) : d250011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247725, d248812, d250011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247725, d248812, d250011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d119118 q = 1) (hb : d157058 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d119118, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d119118, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247730 q = 1) (hb : d248817 q = 1) : d250016 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247730, d248817, d250016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247730, d248817, d250016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247731 q = 1) (hb : d248818 q = 1) : d250017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247731, d248818, d250017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247731, d248818, d250017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62573 (p : Pattern) (ha : d247737 p = 1) (hb : d248824 p = 1) : d250023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247728 q = 1) (hb : d248815 q = 1) : d250014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247728, d248815, d250014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62571 q ha hb
    | true =>
      simp only [d247728, d248815, d250014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247729 q = 1) (hb : d248816 q = 1) : d250015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247729, d248816, d250015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247729, d248816, d250015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247732 q = 1) (hb : d248819 q = 1) : d250018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62572 q ha hb
    | true =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247733 q = 1) (hb : d248820 q = 1) : d250019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247734 q = 1) (hb : d248821 q = 1) : d250020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247734, d248821, d250020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247734, d248821, d250020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247735 q = 1) (hb : d248822 q = 1) : d250021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247735, d248822, d250021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247735, d248822, d250021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247736 q = 1) (hb : d248823 q = 1) : d250022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247736, d248823, d250022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247736, d248823, d250022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247737 q = 1) (hb : d248824 q = 1) : d250023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247737, d248824, d250023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247737, d248824, d250023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62574 (p : Pattern) (ha : d247741 p = 1) (hb : d248828 p = 1) : d250027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247732 q = 1) (hb : d248819 q = 1) : d250018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62572 q ha hb
    | true =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247733 q = 1) (hb : d248820 q = 1) : d250019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119129 q = 1) (hb : d157069 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d119129, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62537 q ha hb
    | true =>
      simp only [d119129, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d119130 q = 1) (hb : d157070 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d119130, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119130, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247738 q = 1) (hb : d248825 q = 1) : d250024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247738, d248825, d250024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247738, d248825, d250024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247739 q = 1) (hb : d248826 q = 1) : d250025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247739, d248826, d250025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247739, d248826, d250025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247740 q = 1) (hb : d248827 q = 1) : d250026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247740, d248827, d250026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247740, d248827, d250026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247741 q = 1) (hb : d248828 q = 1) : d250027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247741, d248828, d250027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247741, d248828, d250027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62575 (p : Pattern) (ha : d247748 p = 1) (hb : d248834 p = 1) : d250027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247732 q = 1) (hb : d248819 q = 1) : d250018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62572 q ha hb
    | true =>
      simp only [d247732, d248819, d250018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247733 q = 1) (hb : d248820 q = 1) : d250019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247733, d248820, d250019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247745 q = 1) (hb : d248831 q = 1) : d250024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247745, d248831, d250024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247745, d248831, d250024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247746 q = 1) (hb : d248832 q = 1) : d250025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247746, d248832, d250025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247746, d248832, d250025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247747 q = 1) (hb : d248833 q = 1) : d250026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247747, d248833, d250026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247747, d248833, d250026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247748 q = 1) (hb : d248834 q = 1) : d250027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247748, d248834, d250027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247748, d248834, d250027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62576 (p : Pattern) (ha : d247754 p = 1) (hb : d248840 p = 1) : d250035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247742 q = 1) (hb : d248829 q = 1) : d250028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247742, d248829, d250028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62573 q ha hb
    | true =>
      simp only [d247742, d248829, d250028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62574 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247744 q = 1) (hb : d248830 q = 1) : d250029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247744, d248830, d250029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247744, d248830, d250029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d247749 q = 1) (hb : d248835 q = 1) : d250030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247749, d248835, d250030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62575 q ha hb
    | true =>
      simp only [d247749, d248835, d250030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247750 q = 1) (hb : d248836 q = 1) : d250031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247750, d248836, d250031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247750, d248836, d250031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247751 q = 1) (hb : d248837 q = 1) : d250032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247751, d248837, d250032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247751, d248837, d250032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247752 q = 1) (hb : d248838 q = 1) : d250033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247752, d248838, d250033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247752, d248838, d250033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247753 q = 1) (hb : d248839 q = 1) : d250034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247753, d248839, d250034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247753, d248839, d250034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247754 q = 1) (hb : d248840 q = 1) : d250035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247754, d248840, d250035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247754, d248840, d250035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62577 (p : Pattern) (ha : d247760 p = 1) (hb : d248846 p = 1) : d250041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247626 q = 1) (hb : d248692 q = 1) : d249915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247626, d248692, d249915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247626, d248692, d249915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62544 q ha hb
  have h2 (q : Pattern) (ha : d247627 q = 1) (hb : d248693 q = 1) : d249916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247627, d248693, d249916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247627, d248693, d249916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247635 q = 1) (hb : d248701 q = 1) : d249924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247635, d248701, d249924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62544 q ha hb
    | true =>
      simp only [d247635, d248701, d249924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62546 q ha hb
  have h4 (q : Pattern) (ha : d247636 q = 1) (hb : d248702 q = 1) : d249925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247636, d248702, d249925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247636, d248702, d249925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247637 q = 1) (hb : d248703 q = 1) : d249926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247637, d248703, d249926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247637, d248703, d249926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247698 q = 1) (hb : d248776 q = 1) : d249984 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247698, d248776, d249984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62558 q ha hb
    | true =>
      simp only [d247698, d248776, d249984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62565 q ha hb
  have h7 (q : Pattern) (ha : d247700 q = 1) (hb : d248778 q = 1) : d249986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247700, d248778, d249986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62566 q ha hb
    | true =>
      simp only [d247700, d248778, d249986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62534 q ha hb
  have h8 (q : Pattern) (ha : d247701 q = 1) (hb : d248779 q = 1) : d249987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247701, d248779, d249987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247701, d248779, d249987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247702 q = 1) (hb : d248780 q = 1) : d249988 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247702, d248780, d249988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247702, d248780, d249988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d247703 q = 1) (hb : d248781 q = 1) : d249989 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247703, d248781, d249989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247703, d248781, d249989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247707 q = 1) (hb : d248785 q = 1) : d249993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247707, d248785, d249993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247707, d248785, d249993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62567 q ha hb
  have h12 (q : Pattern) (ha : d119084 q = 1) (hb : d157021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119084, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119084, d157021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62535 q ha hb
  have h13 (q : Pattern) (ha : d247708 q = 1) (hb : d248786 q = 1) : d249994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247708, d248786, d249994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247708, d248786, d249994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247709 q = 1) (hb : d248787 q = 1) : d249995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247709, d248787, d249995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247709, d248787, d249995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d247710 q = 1) (hb : d248788 q = 1) : d249996 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247710, d248788, d249996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d247710, d248788, d249996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d247711 q = 1) (hb : d248789 q = 1) : d249997 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247711, d248789, d249997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247711, d248789, d249997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d247755 q = 1) (hb : d248841 q = 1) : d250036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247755, d248841, d250036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247755, d248841, d250036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62576 q ha hb
  have h18 (q : Pattern) (ha : d119159 q = 1) (hb : d157098 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d119159, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d119159, d157098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62539 q ha hb
  have h19 (q : Pattern) (ha : d247756 q = 1) (hb : d248842 q = 1) : d250037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247756, d248842, d250037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d247756, d248842, d250037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d247757 q = 1) (hb : d248843 q = 1) : d250038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247757, d248843, d250038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d247757, d248843, d250038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d247758 q = 1) (hb : d248844 q = 1) : d250039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247758, d248844, d250039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d247758, d248844, d250039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d247759 q = 1) (hb : d248845 q = 1) : d250040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247759, d248845, d250040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d247759, d248845, d250040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d247760 q = 1) (hb : d248846 q = 1) : d250041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d247760, d248846, d250041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d247760, d248846, d250041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62578 (p : Pattern) (ha : d247766 p = 1) (hb : d248852 p = 1) : d250047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247761 q = 1) (hb : d248847 q = 1) : d250042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d247761, d248847, d250042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247761, d248847, d250042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62577 q ha hb
  have h2 (q : Pattern) (ha : d247762 q = 1) (hb : d248848 q = 1) : d250043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d247762, d248848, d250043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247762, d248848, d250043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247763 q = 1) (hb : d248849 q = 1) : d250044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d247763, d248849, d250044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247763, d248849, d250044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247764 q = 1) (hb : d248850 q = 1) : d250045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d247764, d248850, d250045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247764, d248850, d250045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247765 q = 1) (hb : d248851 q = 1) : d250046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d247765, d248851, d250046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247765, d248851, d250046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247766 q = 1) (hb : d248852 q = 1) : d250047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d247766, d248852, d250047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247766, d248852, d250047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62579 (p : Pattern) (ha : d101363 p = 1) (hb : d157124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101363 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d1116 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1116, d52697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1132 q = 1) (hb : d52713 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, d52713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1132, d52713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d9841 q = 1) (hb : d101362 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d101362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9841, d101362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9842 q = 1) (hb : d101363 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d101363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9842, d101363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d101363 q = 1) (hb : d157124 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62580 (p : Pattern) (ha : d157135 p = 1) (hb : d247786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157125 q = 1) (hb : d247782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d157125, d247782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62579 q hb ha
    | true =>
      simp only [d157125, d247782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d157126 q = 1) (hb : d247783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d157126, d247783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157126, d247783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d157127 q = 1) (hb : d247784 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d157127, d247784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157127, d247784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d157128 q = 1) (hb : d247785 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d157128, d247785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157128, d247785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d157134 q = 1) (hb : d247786 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d157134, d247786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d157134, d247786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d247786 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d157135 q = 1) (hb : d247786 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62581 (p : Pattern) (ha : d101291 p = 1) (hb : d248855 p = 1) : d249941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101291 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26079 q = 1) (hb : d101289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26079, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26079, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d25767 q = 1) : d25767 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d26080 q = 1) (hb : d101290 q = 1) : d249939 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26080, d101290, d249939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26080, d101290, d249939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d26081 q = 1) (hb : d101291 q = 1) : d249940 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26081, d101291, d249940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26081, d101291, d249940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d101291 q = 1) (hb : d248855 q = 1) : d249941 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248855, d249941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248855, d249941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62582 (p : Pattern) (ha : d101319 p = 1) (hb : d248860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26089 q = 1) (hb : d101316 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26089, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26089, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26090 q = 1) (hb : d101318 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26090, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26090, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26091 q = 1) (hb : d101319 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26091, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26091, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d101319 q = 1) (hb : d248860 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62583 (p : Pattern) (ha : d247777 p = 1) (hb : d248866 p = 1) : d249947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247769 q = 1) (hb : d248856 q = 1) : d249942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247769, d248856, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62581 q ha hb
    | true =>
      simp only [d247769, d248856, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247770 q = 1) (hb : d248857 q = 1) : d249943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247770, d248857, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247770, d248857, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247771 q = 1) (hb : d248858 q = 1) : d249944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247771, d248858, d249944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247771, d248858, d249944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247772 q = 1) (hb : d248859 q = 1) : d249945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247772, d248859, d249945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247772, d248859, d249945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247773 q = 1) (hb : d248861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
    | true =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247774 q = 1) (hb : d248862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247775 q = 1) (hb : d248863 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247775, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247775, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247776 q = 1) (hb : d248864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247776, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247776, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247777 q = 1) (hb : d248865 q = 1) : d249946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247777, d248865, d249946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247777, d248865, d249946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247777 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d247777 q = 1) (hb : d248866 q = 1) : d249947 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248866, d249947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248866, d249947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62584 (p : Pattern) (ha : d25432 p = 1) (hb : d51983 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d128 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h4 (q : Pattern) (ha : d129 q = 1) (hb : d51980 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d130 q = 1) (hb : d51981 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h8 (q : Pattern) (ha : d131 q = 1) (hb : d51982 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25432 q = 1) (hb : d51983 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d25432, d51983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25432, d51983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62585 (p : Pattern) (ha : d101319 p = 1) (hb : d248867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101068 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26089 q = 1) (hb : d101316 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26089, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26089, d101316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25433 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62584 q ha hb
    | true =>
      simp only [d25433, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d25434 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25434, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d25435 q = 1) (hb : d101317 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25435, d101317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25435, d101317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d26114 q = 1) (hb : d101318 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26114, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26114, d101318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26115 q = 1) (hb : d101319 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26115, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26115, d101319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d101319 q = 1) (hb : d248867 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62586 (p : Pattern) (ha : d247778 p = 1) (hb : d248873 p = 1) : d250051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247773 q = 1) (hb : d248868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62585 q ha hb
    | true =>
      simp only [d247773, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247774 q = 1) (hb : d248869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247774, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247775 q = 1) (hb : d248870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247775, d248870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247775, d248870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247776 q = 1) (hb : d248871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247776, d248871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247776, d248871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d157128 q = 1) : d157128 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d247778 q = 1) (hb : d248872 q = 1) : d250050 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247778, d248872, d250050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247778, d248872, d250050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d247778 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d247778 q = 1) (hb : d248873 q = 1) : d250051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248873, d250051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248873, d250051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62587 (p : Pattern) (ha : d247793 p = 1) (hb : d248883 p = 1) : d250061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247779 q = 1) (hb : d248874 q = 1) : d250052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62583 q ha hb
    | true =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
  have h2 (q : Pattern) (ha : d247780 q = 1) (hb : d248875 q = 1) : d250053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247781 q = 1) (hb : d248876 q = 1) : d250054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247787 q = 1) (hb : d248877 q = 1) : d250055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
    | true =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62580 q hb ha
  have h5 (q : Pattern) (ha : d247788 q = 1) (hb : d248878 q = 1) : d250056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247789 q = 1) (hb : d248879 q = 1) : d250057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247790 q = 1) (hb : d248880 q = 1) : d250058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247791 q = 1) (hb : d248881 q = 1) : d250059 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247791, d248881, d250059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247791, d248881, d250059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247792 q = 1) (hb : d248882 q = 1) : d250060 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247792, d248882, d250060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247792, d248882, d250060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247793 q = 1) (hb : d248883 q = 1) : d250061 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247793, d248883, d250061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247793, d248883, d250061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62588 (p : Pattern) (ha : d247797 p = 1) (hb : d248887 p = 1) : d250065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247787 q = 1) (hb : d248877 q = 1) : d250055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
    | true =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62580 q hb ha
  have h2 (q : Pattern) (ha : d247788 q = 1) (hb : d248878 q = 1) : d250056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247789 q = 1) (hb : d248879 q = 1) : d250057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247791 q = 1) (hb : d248881 q = 1) : d250059 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247791, d248881, d250059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247791, d248881, d250059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247796 q = 1) (hb : d248886 q = 1) : d250064 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247796, d248886, d250064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247796, d248886, d250064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247797 q = 1) (hb : d248887 q = 1) : d250065 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247797, d248887, d250065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247797, d248887, d250065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62589 (p : Pattern) (ha : d247803 p = 1) (hb : d248893 p = 1) : d250071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247801 q = 1) (hb : d248891 q = 1) : d250069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247802 q = 1) (hb : d248892 q = 1) : d250070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247802, d248892, d250070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247802, d248892, d250070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247803 q = 1) (hb : d248893 q = 1) : d250071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247803, d248893, d250071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247803, d248893, d250071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62590 (p : Pattern) (ha : d247807 p = 1) (hb : d248897 p = 1) : d250075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247805 q = 1) (hb : d248895 q = 1) : d250073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247806 q = 1) (hb : d248896 q = 1) : d250074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247806, d248896, d250074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247806, d248896, d250074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247807 q = 1) (hb : d248897 q = 1) : d250075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247807, d248897, d250075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247807, d248897, d250075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62591 (p : Pattern) (ha : d247813 p = 1) (hb : d248903 p = 1) : d250081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247808 q = 1) (hb : d248898 q = 1) : d250076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
    | true =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
  have h2 (q : Pattern) (ha : d247809 q = 1) (hb : d248899 q = 1) : d250077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247810 q = 1) (hb : d248900 q = 1) : d250078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247811 q = 1) (hb : d248901 q = 1) : d250079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247812 q = 1) (hb : d248902 q = 1) : d250080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247813 q = 1) (hb : d248903 q = 1) : d250081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247813, d248903, d250081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247813, d248903, d250081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62592 (p : Pattern) (ha : d247816 p = 1) (hb : d248906 p = 1) : d250084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247801 q = 1) (hb : d248891 q = 1) : d250069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247802 q = 1) (hb : d248892 q = 1) : d250070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247802, d248892, d250070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247802, d248892, d250070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247816 q = 1) (hb : d248906 q = 1) : d250084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247816, d248906, d250084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247816, d248906, d250084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62593 (p : Pattern) (ha : d247817 p = 1) (hb : d248907 p = 1) : d250085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247805 q = 1) (hb : d248895 q = 1) : d250073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247806 q = 1) (hb : d248896 q = 1) : d250074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247806, d248896, d250074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247806, d248896, d250074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247817 q = 1) (hb : d248907 q = 1) : d250085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247817, d248907, d250085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247817, d248907, d250085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62594 (p : Pattern) (ha : d247823 p = 1) (hb : d248913 p = 1) : d250091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247808 q = 1) (hb : d248898 q = 1) : d250076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
    | true =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
  have h2 (q : Pattern) (ha : d247809 q = 1) (hb : d248899 q = 1) : d250077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247810 q = 1) (hb : d248900 q = 1) : d250078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247811 q = 1) (hb : d248901 q = 1) : d250079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247812 q = 1) (hb : d248902 q = 1) : d250080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247818 q = 1) (hb : d248908 q = 1) : d250086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62592 q ha hb
    | true =>
      simp only [d247818, d248908, d250086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62593 q ha hb
  have h7 (q : Pattern) (ha : d247819 q = 1) (hb : d248909 q = 1) : d250087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247819, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247819, d248909, d250087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247820 q = 1) (hb : d248910 q = 1) : d250088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247820, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247820, d248910, d250088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247821 q = 1) (hb : d248911 q = 1) : d250089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247821, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247821, d248911, d250089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247822 q = 1) (hb : d248912 q = 1) : d250090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247822, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247822, d248912, d250090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247823 q = 1) (hb : d248913 q = 1) : d250091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247823, d248913, d250091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247823, d248913, d250091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62595 (p : Pattern) (ha : d247828 p = 1) (hb : d248918 p = 1) : d250096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247801 q = 1) (hb : d248891 q = 1) : d250069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247827 q = 1) (hb : d248917 q = 1) : d250095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247827, d248917, d250095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247827, d248917, d250095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247828 q = 1) (hb : d248918 q = 1) : d250096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247828, d248918, d250096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247828, d248918, d250096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62596 (p : Pattern) (ha : d247830 p = 1) (hb : d248920 p = 1) : d250098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247805 q = 1) (hb : d248895 q = 1) : d250073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247829 q = 1) (hb : d248919 q = 1) : d250097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247829, d248919, d250097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247829, d248919, d250097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247830 q = 1) (hb : d248920 q = 1) : d250098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247830, d248920, d250098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247830, d248920, d250098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62597 (p : Pattern) (ha : d247837 p = 1) (hb : d248927 p = 1) : d250105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247835 q = 1) (hb : d248925 q = 1) : d250103 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247835, d248925, d250103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247835, d248925, d250103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247836 q = 1) (hb : d248926 q = 1) : d250104 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247836, d248926, d250104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247836, d248926, d250104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247837 q = 1) (hb : d248927 q = 1) : d250105 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247837, d248927, d250105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247837, d248927, d250105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62598 (p : Pattern) (ha : d247840 p = 1) (hb : d248930 p = 1) : d250108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247838 q = 1) (hb : d248928 q = 1) : d250106 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247838, d248928, d250106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247838, d248928, d250106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247839 q = 1) (hb : d248929 q = 1) : d250107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247839, d248929, d250107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247839, d248929, d250107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247840 q = 1) (hb : d248930 q = 1) : d250108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247840, d248930, d250108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247840, d248930, d250108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62599 (p : Pattern) (ha : d247778 p = 1) (hb : d248950 p = 1) : d250051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247773 q = 1) (hb : d248861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
    | true =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247774 q = 1) (hb : d248862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247775 q = 1) (hb : d248863 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247775, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247775, d248863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247776 q = 1) (hb : d248864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247776, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247776, d248864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d157128 q = 1) : d157128 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d247778 q = 1) (hb : d248949 q = 1) : d250050 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247778, d248949, d250050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247778, d248949, d250050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d247778 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d247778 q = 1) (hb : d248950 q = 1) : d250051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248950, d250051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248950, d250051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62600 (p : Pattern) (ha : d101282 p = 1) (hb : d248934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101282 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9759 q = 1) (hb : d101280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d101280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9759, d101280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9760 q = 1) (hb : d101281 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9760, d101281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9760, d101281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9761 q = 1) (hb : d101282 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9761, d101282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9761, d101282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d101282 q = 1) (hb : d248934 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62601 (p : Pattern) (ha : d101291 p = 1) (hb : d248939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101291 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d26079 q = 1) (hb : d101289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26079, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26079, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26098 q = 1) (hb : d101290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26098, d101290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26098, d101290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d26099 q = 1) (hb : d101291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26099, d101291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26099, d101291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d101291 q = 1) (hb : d248939 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d248939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62602 (p : Pattern) (ha : d247848 p = 1) (hb : d248945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247844 q = 1) (hb : d248935 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247844, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62600 q ha hb
    | true =>
      simp only [d247844, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247845 q = 1) (hb : d248936 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247845, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247845, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247846 q = 1) (hb : d248937 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247846, d248937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247846, d248937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247847 q = 1) (hb : d248938 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247847, d248938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247847, d248938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247769 q = 1) (hb : d248940 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247769, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62601 q ha hb
    | true =>
      simp only [d247769, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247770 q = 1) (hb : d248941 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247770, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247770, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247771 q = 1) (hb : d248942 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247771, d248942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247771, d248942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247772 q = 1) (hb : d248943 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247772, d248943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247772, d248943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247848 q = 1) (hb : d248944 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247848, d248944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247848, d248944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d247848 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d247848 q = 1) (hb : d248945 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d248945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62603 (p : Pattern) (ha : d247854 p = 1) (hb : d248956 p = 1) : d250117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247849 q = 1) (hb : d248946 q = 1) : d250112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247849, d248946, d250112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62602 q ha hb
    | true =>
      simp only [d247849, d248946, d250112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62583 q ha hb
  have h2 (q : Pattern) (ha : d247850 q = 1) (hb : d248947 q = 1) : d250113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247850, d248947, d250113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247850, d248947, d250113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247851 q = 1) (hb : d248948 q = 1) : d250114 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247851, d248948, d250114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247851, d248948, d250114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247779 q = 1) (hb : d248951 q = 1) : d250052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247779, d248951, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62583 q ha hb
    | true =>
      simp only [d247779, d248951, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62599 q ha hb
  have h5 (q : Pattern) (ha : d247780 q = 1) (hb : d248952 q = 1) : d250053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247780, d248952, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247780, d248952, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247781 q = 1) (hb : d248953 q = 1) : d250054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247781, d248953, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247781, d248953, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247852 q = 1) (hb : d248954 q = 1) : d250115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247852, d248954, d250115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247852, d248954, d250115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247779 q = 1) (hb : d248874 q = 1) : d250052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62583 q ha hb
    | true =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
  have h9 (q : Pattern) (ha : d247780 q = 1) (hb : d248875 q = 1) : d250053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247781 q = 1) (hb : d248876 q = 1) : d250054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247787 q = 1) (hb : d248877 q = 1) : d250055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
    | true =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62580 q hb ha
  have h12 (q : Pattern) (ha : d247788 q = 1) (hb : d248878 q = 1) : d250056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d247789 q = 1) (hb : d248879 q = 1) : d250057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247790 q = 1) (hb : d248880 q = 1) : d250058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247853 q = 1) (hb : d248955 q = 1) : d250116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247853, d248955, d250116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247853, d248955, d250116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247854 q = 1) (hb : d248956 q = 1) : d250117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247854, d248956, d250117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247854, d248956, d250117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62604 (p : Pattern) (ha : d247860 p = 1) (hb : d248962 p = 1) : d250123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247855 q = 1) (hb : d248957 q = 1) : d250118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247855, d248957, d250118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62603 q ha hb
    | true =>
      simp only [d247855, d248957, d250118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247856 q = 1) (hb : d248958 q = 1) : d250119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247856, d248958, d250119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247856, d248958, d250119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247857 q = 1) (hb : d248959 q = 1) : d250120 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247857, d248959, d250120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247857, d248959, d250120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247858 q = 1) (hb : d248960 q = 1) : d250121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247858, d248960, d250121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247858, d248960, d250121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247859 q = 1) (hb : d248961 q = 1) : d250122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247859, d248961, d250122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247859, d248961, d250122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247860 q = 1) (hb : d248962 q = 1) : d250123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247860, d248962, d250123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247860, d248962, d250123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62605 (p : Pattern) (ha : d247868 p = 1) (hb : d248883 p = 1) : d250131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247779 q = 1) (hb : d248874 q = 1) : d250052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62583 q ha hb
    | true =>
      simp only [d247779, d248874, d250052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
  have h2 (q : Pattern) (ha : d247780 q = 1) (hb : d248875 q = 1) : d250053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247780, d248875, d250053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247781 q = 1) (hb : d248876 q = 1) : d250054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247781, d248876, d250054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247787 q = 1) (hb : d248877 q = 1) : d250055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
    | true =>
      simp only [d247787, d248877, d250055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62580 q hb ha
  have h5 (q : Pattern) (ha : d247788 q = 1) (hb : d248878 q = 1) : d250056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247788, d248878, d250056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247789 q = 1) (hb : d248879 q = 1) : d250057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247789, d248879, d250057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247790 q = 1) (hb : d248880 q = 1) : d250058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247790, d248880, d250058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157135 q = 1) : d157135 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d247863 q = 1) (hb : d248877 q = 1) : d250126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247863, d248877, d250126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62586 q ha hb
    | true =>
      simp only [d247863, d248877, d250126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247864 q = 1) (hb : d248878 q = 1) : d250127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247864, d248878, d250127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247864, d248878, d250127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247865 q = 1) (hb : d248879 q = 1) : d250128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247865, d248879, d250128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247865, d248879, d250128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247866 q = 1) (hb : d248881 q = 1) : d250129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247866, d248881, d250129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247866, d248881, d250129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247867 q = 1) (hb : d248882 q = 1) : d250130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247867, d248882, d250130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247867, d248882, d250130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247868 q = 1) (hb : d248883 q = 1) : d250131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247868, d248883, d250131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247868, d248883, d250131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62606 (p : Pattern) (ha : d247874 p = 1) (hb : d248968 p = 1) : d250137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247869 q = 1) (hb : d248884 q = 1) : d250132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247869, d248884, d250132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62605 q ha hb
    | true =>
      simp only [d247869, d248884, d250132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247870 q = 1) (hb : d248885 q = 1) : d250133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247870, d248885, d250133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247870, d248885, d250133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247871 q = 1) (hb : d248965 q = 1) : d250134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247871, d248965, d250134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247871, d248965, d250134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247872 q = 1) (hb : d248966 q = 1) : d250135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247872, d248966, d250135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247872, d248966, d250135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247873 q = 1) (hb : d248967 q = 1) : d250136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247873, d248967, d250136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247873, d248967, d250136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247874 q = 1) (hb : d248968 q = 1) : d250137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247874, d248968, d250137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247874, d248968, d250137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62607 (p : Pattern) (ha : d247880 p = 1) (hb : d248974 p = 1) : d250143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247831 q = 1) (hb : d248921 q = 1) : d250099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247831, d248921, d250099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62595 q ha hb
    | true =>
      simp only [d247831, d248921, d250099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62596 q ha hb
  have h2 (q : Pattern) (ha : d247832 q = 1) (hb : d248922 q = 1) : d250100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247832, d248922, d250100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247832, d248922, d250100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247833 q = 1) (hb : d248923 q = 1) : d250101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247833, d248923, d250101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247833, d248923, d250101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247834 q = 1) (hb : d248924 q = 1) : d250102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247834, d248924, d250102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247834, d248924, d250102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247841 q = 1) (hb : d248931 q = 1) : d250109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247841, d248931, d250109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62597 q ha hb
    | true =>
      simp only [d247841, d248931, d250109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62598 q ha hb
  have h6 (q : Pattern) (ha : d247842 q = 1) (hb : d248932 q = 1) : d250110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247842, d248932, d250110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247842, d248932, d250110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247843 q = 1) (hb : d248933 q = 1) : d250111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247843, d248933, d250111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247843, d248933, d250111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247861 q = 1) (hb : d248963 q = 1) : d250124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247861, d248963, d250124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62604 q ha hb
    | true =>
      simp only [d247861, d248963, d250124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247862 q = 1) (hb : d248964 q = 1) : d250125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247862, d248964, d250125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247862, d248964, d250125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d247875 q = 1) (hb : d248969 q = 1) : d250138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247875, d248969, d250138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62606 q ha hb
    | true =>
      simp only [d247875, d248969, d250138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d247876 q = 1) (hb : d248970 q = 1) : d250139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247876, d248970, d250139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247876, d248970, d250139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247877 q = 1) (hb : d248971 q = 1) : d250140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247877, d248971, d250140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247877, d248971, d250140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247878 q = 1) (hb : d248972 q = 1) : d250141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247878, d248972, d250141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247878, d248972, d250141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247879 q = 1) (hb : d248973 q = 1) : d250142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247879, d248973, d250142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247879, d248973, d250142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247880 q = 1) (hb : d248974 q = 1) : d250143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247880, d248974, d250143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247880, d248974, d250143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62608 (p : Pattern) (ha : d247881 p = 1) (hb : d248975 p = 1) : d250144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247801 q = 1) (hb : d248891 q = 1) : d250069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247801, d248891, d250069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247827 q = 1) (hb : d248917 q = 1) : d250095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247827, d248917, d250095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247827, d248917, d250095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247881 q = 1) (hb : d248975 q = 1) : d250144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247881, d248975, d250144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247881, d248975, d250144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62609 (p : Pattern) (ha : d247882 p = 1) (hb : d248976 p = 1) : d250145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247805 q = 1) (hb : d248895 q = 1) : d250073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247805, d248895, d250073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247829 q = 1) (hb : d248919 q = 1) : d250097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247829, d248919, d250097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247829, d248919, d250097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247882 q = 1) (hb : d248976 q = 1) : d250145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247882, d248976, d250145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247882, d248976, d250145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62610 (p : Pattern) (ha : d247887 p = 1) (hb : d248981 p = 1) : d250150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247800 q = 1) (hb : d248890 q = 1) : d250068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247800, d248890, d250068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247835 q = 1) (hb : d248925 q = 1) : d250103 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247835, d248925, d250103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247835, d248925, d250103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247836 q = 1) (hb : d248926 q = 1) : d250104 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247836, d248926, d250104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247836, d248926, d250104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247887 q = 1) (hb : d248981 q = 1) : d250150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247887, d248981, d250150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247887, d248981, d250150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62611 (p : Pattern) (ha : d247888 p = 1) (hb : d248982 p = 1) : d250151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247798 q = 1) (hb : d248888 q = 1) : d250066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62588 q ha hb
    | true =>
      simp only [d247798, d248888, d250066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247799 q = 1) (hb : d248889 q = 1) : d250067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247799, d248889, d250067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247804 q = 1) (hb : d248894 q = 1) : d250072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247804, d248894, d250072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247838 q = 1) (hb : d248928 q = 1) : d250106 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247838, d248928, d250106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247838, d248928, d250106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247839 q = 1) (hb : d248929 q = 1) : d250107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247839, d248929, d250107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247839, d248929, d250107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247888 q = 1) (hb : d248982 q = 1) : d250151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247888, d248982, d250151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247888, d248982, d250151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62612 (p : Pattern) (ha : d247892 p = 1) (hb : d248986 p = 1) : d250155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247855 q = 1) (hb : d248957 q = 1) : d250118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247855, d248957, d250118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62603 q ha hb
    | true =>
      simp only [d247855, d248957, d250118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247856 q = 1) (hb : d248958 q = 1) : d250119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247856, d248958, d250119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247856, d248958, d250119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247794 q = 1) (hb : d248884 q = 1) : d250062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62587 q ha hb
    | true =>
      simp only [d247794, d248884, d250062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247795 q = 1) (hb : d248885 q = 1) : d250063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247795, d248885, d250063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247857 q = 1) (hb : d248959 q = 1) : d250120 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247857, d248959, d250120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247857, d248959, d250120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247858 q = 1) (hb : d248960 q = 1) : d250121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247858, d248960, d250121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247858, d248960, d250121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247859 q = 1) (hb : d248961 q = 1) : d250122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247859, d248961, d250122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247859, d248961, d250122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247892 q = 1) (hb : d248986 q = 1) : d250155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247892, d248986, d250155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247892, d248986, d250155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62613 (p : Pattern) (ha : d247895 p = 1) (hb : d248989 p = 1) : d250158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247869 q = 1) (hb : d248884 q = 1) : d250132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247869, d248884, d250132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62605 q ha hb
    | true =>
      simp only [d247869, d248884, d250132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247870 q = 1) (hb : d248885 q = 1) : d250133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247870, d248885, d250133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247870, d248885, d250133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247871 q = 1) (hb : d248965 q = 1) : d250134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247871, d248965, d250134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247871, d248965, d250134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247872 q = 1) (hb : d248966 q = 1) : d250135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247872, d248966, d250135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247872, d248966, d250135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247873 q = 1) (hb : d248967 q = 1) : d250136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247873, d248967, d250136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247873, d248967, d250136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247895 q = 1) (hb : d248989 q = 1) : d250158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247895, d248989, d250158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247895, d248989, d250158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62614 (p : Pattern) (ha : d247901 p = 1) (hb : d248995 p = 1) : d250164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247831 q = 1) (hb : d248921 q = 1) : d250099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247831, d248921, d250099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62595 q ha hb
    | true =>
      simp only [d247831, d248921, d250099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62596 q ha hb
  have h2 (q : Pattern) (ha : d247832 q = 1) (hb : d248922 q = 1) : d250100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247832, d248922, d250100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247832, d248922, d250100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247833 q = 1) (hb : d248923 q = 1) : d250101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247833, d248923, d250101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247833, d248923, d250101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247834 q = 1) (hb : d248924 q = 1) : d250102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247834, d248924, d250102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247834, d248924, d250102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247841 q = 1) (hb : d248931 q = 1) : d250109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247841, d248931, d250109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62597 q ha hb
    | true =>
      simp only [d247841, d248931, d250109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62598 q ha hb
  have h6 (q : Pattern) (ha : d247842 q = 1) (hb : d248932 q = 1) : d250110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247842, d248932, d250110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247842, d248932, d250110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247843 q = 1) (hb : d248933 q = 1) : d250111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247843, d248933, d250111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247843, d248933, d250111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247861 q = 1) (hb : d248963 q = 1) : d250124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247861, d248963, d250124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62604 q ha hb
    | true =>
      simp only [d247861, d248963, d250124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247862 q = 1) (hb : d248964 q = 1) : d250125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247862, d248964, d250125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247862, d248964, d250125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d247875 q = 1) (hb : d248969 q = 1) : d250138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247875, d248969, d250138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62606 q ha hb
    | true =>
      simp only [d247875, d248969, d250138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d247876 q = 1) (hb : d248970 q = 1) : d250139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247876, d248970, d250139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247876, d248970, d250139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247877 q = 1) (hb : d248971 q = 1) : d250140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247877, d248971, d250140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247877, d248971, d250140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247878 q = 1) (hb : d248972 q = 1) : d250141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247878, d248972, d250141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247878, d248972, d250141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247879 q = 1) (hb : d248973 q = 1) : d250142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247879, d248973, d250142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247879, d248973, d250142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247883 q = 1) (hb : d248977 q = 1) : d250146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247883, d248977, d250146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62608 q ha hb
    | true =>
      simp only [d247883, d248977, d250146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62609 q ha hb
  have h17 (q : Pattern) (ha : d247884 q = 1) (hb : d248978 q = 1) : d250147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247884, d248978, d250147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247884, d248978, d250147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d247885 q = 1) (hb : d248979 q = 1) : d250148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247885, d248979, d250148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d247885, d248979, d250148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d247886 q = 1) (hb : d248980 q = 1) : d250149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247886, d248980, d250149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247886, d248980, d250149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d247889 q = 1) (hb : d248983 q = 1) : d250152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247889, d248983, d250152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62610 q ha hb
    | true =>
      simp only [d247889, d248983, d250152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62611 q ha hb
  have h21 (q : Pattern) (ha : d247890 q = 1) (hb : d248984 q = 1) : d250153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247890, d248984, d250153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247890, d248984, d250153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d247891 q = 1) (hb : d248985 q = 1) : d250154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247891, d248985, d250154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d247891, d248985, d250154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d247893 q = 1) (hb : d248987 q = 1) : d250156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247893, d248987, d250156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62612 q ha hb
    | true =>
      simp only [d247893, d248987, d250156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62592 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d247818 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d247894 q = 1) (hb : d248988 q = 1) : d250157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247894, d248988, d250157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d247894, d248988, d250157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d247896 q = 1) (hb : d248990 q = 1) : d250159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247896, d248990, d250159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62613 q ha hb
    | true =>
      simp only [d247896, d248990, d250159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d247897 q = 1) (hb : d248991 q = 1) : d250160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247897, d248991, d250160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d247897, d248991, d250160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d247898 q = 1) (hb : d248992 q = 1) : d250161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247898, d248992, d250161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d247898, d248992, d250161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d247899 q = 1) (hb : d248993 q = 1) : d250162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247899, d248993, d250162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d247899, d248993, d250162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d247900 q = 1) (hb : d248994 q = 1) : d250163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247900, d248994, d250163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d247900, d248994, d250163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d247901 q = 1) (hb : d248995 q = 1) : d250164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247901, d248995, d250164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247901, d248995, d250164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62615 (p : Pattern) (ha : d247908 p = 1) (hb : d249002 p = 1) : d250171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247808 q = 1) (hb : d248898 q = 1) : d250076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62589 q ha hb
    | true =>
      simp only [d247808, d248898, d250076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
  have h2 (q : Pattern) (ha : d247809 q = 1) (hb : d248899 q = 1) : d250077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247809, d248899, d250077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247810 q = 1) (hb : d248900 q = 1) : d250078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247810, d248900, d250078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247811 q = 1) (hb : d248901 q = 1) : d250079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247811, d248901, d250079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247812 q = 1) (hb : d248902 q = 1) : d250080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247812, d248902, d250080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247903 q = 1) (hb : d248997 q = 1) : d250166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247903, d248997, d250166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
    | true =>
      simp only [d247903, d248997, d250166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247904 q = 1) (hb : d248998 q = 1) : d250167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247904, d248998, d250167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247904, d248998, d250167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247905 q = 1) (hb : d248999 q = 1) : d250168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247905, d248999, d250168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247905, d248999, d250168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247906 q = 1) (hb : d249000 q = 1) : d250169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247906, d249000, d250169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247906, d249000, d250169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247907 q = 1) (hb : d249001 q = 1) : d250170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247907, d249001, d250170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247907, d249001, d250170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247908 q = 1) (hb : d249002 q = 1) : d250171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247908, d249002, d250171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247908, d249002, d250171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62616 (p : Pattern) (ha : d247914 p = 1) (hb : d249008 p = 1) : d250177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247903 q = 1) (hb : d248997 q = 1) : d250166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247903, d248997, d250166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62590 q ha hb
    | true =>
      simp only [d247903, d248997, d250166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247904 q = 1) (hb : d248998 q = 1) : d250167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247904, d248998, d250167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247904, d248998, d250167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247905 q = 1) (hb : d248999 q = 1) : d250168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247905, d248999, d250168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247905, d248999, d250168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247906 q = 1) (hb : d249000 q = 1) : d250169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247906, d249000, d250169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247906, d249000, d250169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247907 q = 1) (hb : d249001 q = 1) : d250170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247907, d249001, d250170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247907, d249001, d250170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247909 q = 1) (hb : d249003 q = 1) : d250172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247909, d249003, d250172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62593 q ha hb
    | true =>
      simp only [d247909, d249003, d250172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247910 q = 1) (hb : d249004 q = 1) : d250173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247910, d249004, d250173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247910, d249004, d250173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247911 q = 1) (hb : d249005 q = 1) : d250174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247911, d249005, d250174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247911, d249005, d250174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247912 q = 1) (hb : d249006 q = 1) : d250175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247912, d249006, d250175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247912, d249006, d250175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247913 q = 1) (hb : d249007 q = 1) : d250176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247913, d249007, d250176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247913, d249007, d250176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247914 q = 1) (hb : d249008 q = 1) : d250177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247914, d249008, d250177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247914, d249008, d250177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62617 (p : Pattern) (ha : d247921 p = 1) (hb : d249015 p = 1) : d250184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247893 q = 1) (hb : d248987 q = 1) : d250156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247893, d248987, d250156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62612 q ha hb
    | true =>
      simp only [d247893, d248987, d250156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62592 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247894 q = 1) (hb : d248988 q = 1) : d250157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247894, d248988, d250157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247894, d248988, d250157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d247896 q = 1) (hb : d248990 q = 1) : d250159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247896, d248990, d250159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62613 q ha hb
    | true =>
      simp only [d247896, d248990, d250159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247897 q = 1) (hb : d248991 q = 1) : d250160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247897, d248991, d250160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247897, d248991, d250160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247898 q = 1) (hb : d248992 q = 1) : d250161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247898, d248992, d250161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247898, d248992, d250161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247919 q = 1) (hb : d249013 q = 1) : d250182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247919, d249013, d250182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247919, d249013, d250182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247920 q = 1) (hb : d249014 q = 1) : d250183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247920, d249014, d250183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247920, d249014, d250183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247921 q = 1) (hb : d249015 q = 1) : d250184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247921, d249015, d250184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247921, d249015, d250184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62618 (p : Pattern) (ha : d247923 p = 1) (hb : d249017 p = 1) : d250186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247909 q = 1) (hb : d249003 q = 1) : d250172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247909, d249003, d250172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62593 q ha hb
    | true =>
      simp only [d247909, d249003, d250172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247910 q = 1) (hb : d249004 q = 1) : d250173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247910, d249004, d250173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247910, d249004, d250173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247911 q = 1) (hb : d249005 q = 1) : d250174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d247911, d249005, d250174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247911, d249005, d250174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247912 q = 1) (hb : d249006 q = 1) : d250175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d247912, d249006, d250175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247912, d249006, d250175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247913 q = 1) (hb : d249007 q = 1) : d250176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d247913, d249007, d250176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247913, d249007, d250176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247923 q = 1) (hb : d249017 q = 1) : d250186 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d247923, d249017, d250186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247923, d249017, d250186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62619 (p : Pattern) (ha : d157324 p = 1) (hb : d247955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157314 q = 1) (hb : d247951 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d157314, d247951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157314, d247951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62579 q hb ha
  have h2 (q : Pattern) (ha : d157125 q = 1) (hb : d247782 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d157125, d247782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62579 q hb ha
    | true =>
      simp only [d157125, d247782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d157315 q = 1) (hb : d247952 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d157315, d247952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157315, d247952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d157126 q = 1) (hb : d247783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d157126, d247783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157126, d247783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d157316 q = 1) (hb : d247953 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d157316, d247953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157316, d247953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d157317 q = 1) (hb : d247954 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d157317, d247954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157317, d247954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d157323 q = 1) (hb : d247955 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d157323, d247955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d157323, d247955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d247955 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d157324 q = 1) (hb : d247955 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62620 (p : Pattern) (ha : d247937 p = 1) (hb : d249032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247929 q = 1) (hb : d249023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247929, d249023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247929, d249023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62600 q ha hb
  have h2 (q : Pattern) (ha : d247844 q = 1) (hb : d248935 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247844, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62600 q ha hb
    | true =>
      simp only [d247844, d248935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247930 q = 1) (hb : d249024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247930, d249024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247930, d249024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247845 q = 1) (hb : d248936 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247845, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247845, d248936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247931 q = 1) (hb : d249025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247931, d249025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247931, d249025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247932 q = 1) (hb : d249026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247932, d249026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247932, d249026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247933 q = 1) (hb : d249027 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247933, d249027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247933, d249027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62601 q ha hb
  have h8 (q : Pattern) (ha : d247769 q = 1) (hb : d248940 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247769, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62601 q ha hb
    | true =>
      simp only [d247769, d248940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247934 q = 1) (hb : d249028 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247934, d249028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247934, d249028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247770 q = 1) (hb : d248941 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247770, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247770, d248941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d247935 q = 1) (hb : d249029 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247935, d249029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247935, d249029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247936 q = 1) (hb : d249030 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247936, d249030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247936, d249030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247937 q = 1) (hb : d249031 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247937, d249031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247937, d249031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247937 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247937 q = 1) (hb : d249032 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62621 (p : Pattern) (ha : d247942 p = 1) (hb : d249042 p = 1) : d250003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247933 q = 1) (hb : d249033 q = 1) : d249998 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247933, d249033, d249998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247933, d249033, d249998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62581 q ha hb
  have h2 (q : Pattern) (ha : d247769 q = 1) (hb : d248856 q = 1) : d249942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247769, d248856, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62581 q ha hb
    | true =>
      simp only [d247769, d248856, d249942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247934 q = 1) (hb : d249034 q = 1) : d249999 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247934, d249034, d249999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247934, d249034, d249999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247770 q = 1) (hb : d248857 q = 1) : d249943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247770, d248857, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247770, d248857, d249943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247935 q = 1) (hb : d249035 q = 1) : d250000 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247935, d249035, d250000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247935, d249035, d250000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247936 q = 1) (hb : d249036 q = 1) : d250001 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247936, d249036, d250001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247936, d249036, d250001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247938 q = 1) (hb : d249037 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247938, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247938, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
  have h8 (q : Pattern) (ha : d247773 q = 1) (hb : d248861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
    | true =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247939 q = 1) (hb : d249038 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247939, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247939, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247774 q = 1) (hb : d248862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d247940 q = 1) (hb : d249039 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247940, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247940, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247941 q = 1) (hb : d249040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247941, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247941, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247942 q = 1) (hb : d249041 q = 1) : d250002 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247942, d249041, d250002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247942, d249041, d250002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d247942 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d247942 q = 1) (hb : d249042 q = 1) : d250003 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249042, d250003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249042, d250003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62622 (p : Pattern) (ha : d247946 p = 1) (hb : d249047 p = 1) : d250196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247938 q = 1) (hb : d249037 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247938, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247938, d249037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
  have h2 (q : Pattern) (ha : d247773 q = 1) (hb : d248861 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62582 q ha hb
    | true =>
      simp only [d247773, d248861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247939 q = 1) (hb : d249038 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247939, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247939, d249038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247774 q = 1) (hb : d248862 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247774, d248862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247940 q = 1) (hb : d249039 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247940, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247940, d249039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247941 q = 1) (hb : d249040 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247941, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247941, d249040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d157317 q = 1) : d157317 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d247946 q = 1) (hb : d249046 q = 1) : d250195 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247946, d249046, d250195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247946, d249046, d250195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247946 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247946 q = 1) (hb : d249047 q = 1) : d250196 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249047, d250196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249047, d250196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62623 (p : Pattern) (ha : d247946 p = 1) (hb : d249057 p = 1) : d250196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247938 q = 1) (hb : d249052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247938, d249052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247938, d249052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62585 q ha hb
  have h2 (q : Pattern) (ha : d247773 q = 1) (hb : d248868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d247773, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62585 q ha hb
    | true =>
      simp only [d247773, d248868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247939 q = 1) (hb : d249053 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247939, d249053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247939, d249053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247774 q = 1) (hb : d248869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d247774, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247774, d248869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247940 q = 1) (hb : d249054 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247940, d249054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247940, d249054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247941 q = 1) (hb : d249055 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d247941, d249055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247941, d249055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d157317 q = 1) : d157317 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d247946 q = 1) (hb : d249056 q = 1) : d250195 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d247946, d249056, d250195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247946, d249056, d250195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d247946 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d247946 q = 1) (hb : d249057 q = 1) : d250196 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249057, d250196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249057, d250196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62624 (p : Pattern) (ha : d247961 p = 1) (hb : d249066 p = 1) : d250206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247943 q = 1) (hb : d249043 q = 1) : d250192 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247943, d249043, d250192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62620 q ha hb
    | true =>
      simp only [d247943, d249043, d250192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62621 q ha hb
  have h2 (q : Pattern) (ha : d247944 q = 1) (hb : d249044 q = 1) : d250193 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247944, d249044, d250193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247944, d249044, d250193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247945 q = 1) (hb : d249045 q = 1) : d250194 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247945, d249045, d250194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247945, d249045, d250194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247947 q = 1) (hb : d249048 q = 1) : d250197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247947, d249048, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62621 q ha hb
    | true =>
      simp only [d247947, d249048, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62622 q ha hb
  have h5 (q : Pattern) (ha : d247948 q = 1) (hb : d249049 q = 1) : d250198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247948, d249049, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247948, d249049, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247949 q = 1) (hb : d249050 q = 1) : d250199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247949, d249050, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247949, d249050, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247950 q = 1) (hb : d249051 q = 1) : d250200 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247950, d249051, d250200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247950, d249051, d250200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247947 q = 1) (hb : d249058 q = 1) : d250197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62621 q ha hb
    | true =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
  have h9 (q : Pattern) (ha : d247948 q = 1) (hb : d249059 q = 1) : d250198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247949 q = 1) (hb : d249060 q = 1) : d250199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247956 q = 1) (hb : d249061 q = 1) : d250201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
    | true =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62619 q hb ha
  have h12 (q : Pattern) (ha : d247957 q = 1) (hb : d249062 q = 1) : d250202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d247958 q = 1) (hb : d249063 q = 1) : d250203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247959 q = 1) (hb : d249064 q = 1) : d250204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d247960 q = 1) (hb : d249065 q = 1) : d250205 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247960, d249065, d250205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247960, d249065, d250205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d247961 q = 1) (hb : d249066 q = 1) : d250206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247961, d249066, d250206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d247961, d249066, d250206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62625 (p : Pattern) (ha : d247966 p = 1) (hb : d249071 p = 1) : d250211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247947 q = 1) (hb : d249058 q = 1) : d250197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62621 q ha hb
    | true =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
  have h2 (q : Pattern) (ha : d247948 q = 1) (hb : d249059 q = 1) : d250198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247949 q = 1) (hb : d249060 q = 1) : d250199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247956 q = 1) (hb : d249061 q = 1) : d250201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
    | true =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62619 q hb ha
  have h5 (q : Pattern) (ha : d247957 q = 1) (hb : d249062 q = 1) : d250202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247958 q = 1) (hb : d249063 q = 1) : d250203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247959 q = 1) (hb : d249064 q = 1) : d250204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d247964 q = 1) (hb : d249069 q = 1) : d250209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247964, d249069, d250209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247964, d249069, d250209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d247965 q = 1) (hb : d249070 q = 1) : d250210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247965, d249070, d250210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247965, d249070, d250210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247966 q = 1) (hb : d249071 q = 1) : d250211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247966, d249071, d250211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d247966, d249071, d250211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62626 (p : Pattern) (ha : d247972 p = 1) (hb : d249077 p = 1) : d250217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247962 q = 1) (hb : d249067 q = 1) : d250207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247962, d249067, d250207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62624 q ha hb
    | true =>
      simp only [d247962, d249067, d250207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247963 q = 1) (hb : d249068 q = 1) : d250208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247963, d249068, d250208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247963, d249068, d250208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247967 q = 1) (hb : d249072 q = 1) : d250212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247967, d249072, d250212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62625 q ha hb
    | true =>
      simp only [d247967, d249072, d250212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247968 q = 1) (hb : d249073 q = 1) : d250213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247968, d249073, d250213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247968, d249073, d250213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247969 q = 1) (hb : d249074 q = 1) : d250214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247969, d249074, d250214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247969, d249074, d250214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247970 q = 1) (hb : d249075 q = 1) : d250215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247970, d249075, d250215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247970, d249075, d250215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247971 q = 1) (hb : d249076 q = 1) : d250216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247971, d249076, d250216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247971, d249076, d250216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247972 q = 1) (hb : d249077 q = 1) : d250217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247972, d249077, d250217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247972, d249077, d250217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62627 (p : Pattern) (ha : d247974 p = 1) (hb : d249079 p = 1) : d250219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247956 q = 1) (hb : d249061 q = 1) : d250201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
    | true =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62619 q hb ha
  have h2 (q : Pattern) (ha : d247957 q = 1) (hb : d249062 q = 1) : d250202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247958 q = 1) (hb : d249063 q = 1) : d250203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247964 q = 1) (hb : d249069 q = 1) : d250209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247964, d249069, d250209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247964, d249069, d250209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247973 q = 1) (hb : d249078 q = 1) : d250218 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247973, d249078, d250218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247973, d249078, d250218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247974 q = 1) (hb : d249079 q = 1) : d250219 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247974, d249079, d250219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247974, d249079, d250219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62628 (p : Pattern) (ha : d247980 p = 1) (hb : d249085 p = 1) : d250225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247967 q = 1) (hb : d249072 q = 1) : d250212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247967, d249072, d250212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62625 q ha hb
    | true =>
      simp only [d247967, d249072, d250212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247968 q = 1) (hb : d249073 q = 1) : d250213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247968, d249073, d250213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247968, d249073, d250213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247975 q = 1) (hb : d249080 q = 1) : d250220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247975, d249080, d250220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62627 q ha hb
    | true =>
      simp only [d247975, d249080, d250220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247976 q = 1) (hb : d249081 q = 1) : d250221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247976, d249081, d250221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247976, d249081, d250221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d247977 q = 1) (hb : d249082 q = 1) : d250222 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247977, d249082, d250222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247977, d249082, d250222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247978 q = 1) (hb : d249083 q = 1) : d250223 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247978, d249083, d250223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247978, d249083, d250223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d247979 q = 1) (hb : d249084 q = 1) : d250224 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247979, d249084, d250224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247979, d249084, d250224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d247980 q = 1) (hb : d249085 q = 1) : d250225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247980, d249085, d250225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247980, d249085, d250225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62629 (p : Pattern) (ha : d247993 p = 1) (hb : d249071 p = 1) : d250233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247947 q = 1) (hb : d249058 q = 1) : d250197 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62621 q ha hb
    | true =>
      simp only [d247947, d249058, d250197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
  have h2 (q : Pattern) (ha : d247948 q = 1) (hb : d249059 q = 1) : d250198 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247948, d249059, d250198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247949 q = 1) (hb : d249060 q = 1) : d250199 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247949, d249060, d250199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d247956 q = 1) (hb : d249061 q = 1) : d250201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
    | true =>
      simp only [d247956, d249061, d250201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62619 q hb ha
  have h5 (q : Pattern) (ha : d247957 q = 1) (hb : d249062 q = 1) : d250202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247957, d249062, d250202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247958 q = 1) (hb : d249063 q = 1) : d250203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247958, d249063, d250203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d247959 q = 1) (hb : d249064 q = 1) : d250204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247959, d249064, d250204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157324 q = 1) : d157324 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d247988 q = 1) (hb : d249061 q = 1) : d250228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d247988, d249061, d250228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62623 q ha hb
    | true =>
      simp only [d247988, d249061, d250228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d247989 q = 1) (hb : d249062 q = 1) : d250229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d247989, d249062, d250229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247989, d249062, d250229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247990 q = 1) (hb : d249063 q = 1) : d250230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d247990, d249063, d250230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247990, d249063, d250230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d247991 q = 1) (hb : d249069 q = 1) : d250231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d247991, d249069, d250231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247991, d249069, d250231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d247992 q = 1) (hb : d249070 q = 1) : d250232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d247992, d249070, d250232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d247992, d249070, d250232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247993 q = 1) (hb : d249071 q = 1) : d250233 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d247993, d249071, d250233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247993, d249071, d250233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62630 (p : Pattern) (ha : d247999 p = 1) (hb : d249091 p = 1) : d250239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247994 q = 1) (hb : d249072 q = 1) : d250234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247994, d249072, d250234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62629 q ha hb
    | true =>
      simp only [d247994, d249072, d250234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247995 q = 1) (hb : d249073 q = 1) : d250235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247995, d249073, d250235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247995, d249073, d250235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247996 q = 1) (hb : d249088 q = 1) : d250236 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247996, d249088, d250236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247996, d249088, d250236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247997 q = 1) (hb : d249089 q = 1) : d250237 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247997, d249089, d250237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247997, d249089, d250237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247998 q = 1) (hb : d249090 q = 1) : d250238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247998, d249090, d250238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247998, d249090, d250238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247999 q = 1) (hb : d249091 q = 1) : d250239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247999, d249091, d250239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247999, d249091, d250239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62631 (p : Pattern) (ha : d248005 p = 1) (hb : d249097 p = 1) : d250245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247981 q = 1) (hb : d249086 q = 1) : d250226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d247981, d249086, d250226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62626 q ha hb
    | true =>
      simp only [d247981, d249086, d250226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62628 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d247986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d247987 q = 1) (hb : d249087 q = 1) : d250227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d247987, d249087, d250227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247987, d249087, d250227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d248000 q = 1) (hb : d249092 q = 1) : d250240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248000, d249092, d250240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62630 q ha hb
    | true =>
      simp only [d248000, d249092, d250240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248001 q = 1) (hb : d249093 q = 1) : d250241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248001, d249093, d250241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248001, d249093, d250241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248002 q = 1) (hb : d249094 q = 1) : d250242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248002, d249094, d250242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248002, d249094, d250242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248003 q = 1) (hb : d249095 q = 1) : d250243 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248003, d249095, d250243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248003, d249095, d250243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248004 q = 1) (hb : d249096 q = 1) : d250244 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248004, d249096, d250244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248004, d249096, d250244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248005 q = 1) (hb : d249097 q = 1) : d250245 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248005, d249097, d250245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248005, d249097, d250245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62632 (p : Pattern) (ha : d247985 p = 1) (hb : d249102 p = 1) : d250250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247975 q = 1) (hb : d249080 q = 1) : d250220 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d247975, d249080, d250220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62627 q ha hb
    | true =>
      simp only [d247975, d249080, d250220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d247976 q = 1) (hb : d249081 q = 1) : d250221 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d247976, d249081, d250221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247976, d249081, d250221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d247982 q = 1) (hb : d249099 q = 1) : d250247 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d247982, d249099, d250247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247982, d249099, d250247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d247983 q = 1) (hb : d249100 q = 1) : d250248 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d247983, d249100, d250248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247983, d249100, d250248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247984 q = 1) (hb : d249101 q = 1) : d250249 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d247984, d249101, d250249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d247984, d249101, d250249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d247985 q = 1) (hb : d249102 q = 1) : d250250 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d247985, d249102, d250250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247985, d249102, d250250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62633 (p : Pattern) (ha : d248012 p = 1) (hb : d249108 p = 1) : d250256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248007 q = 1) (hb : d249103 q = 1) : d250251 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248007, d249103, d250251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62632 q ha hb
    | true =>
      simp only [d248007, d249103, d250251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248008 q = 1) (hb : d249104 q = 1) : d250252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248008, d249104, d250252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248008, d249104, d250252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248009 q = 1) (hb : d249105 q = 1) : d250253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248009, d249105, d250253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248009, d249105, d250253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248010 q = 1) (hb : d249106 q = 1) : d250254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248010, d249106, d250254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248010, d249106, d250254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248011 q = 1) (hb : d249107 q = 1) : d250255 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248011, d249107, d250255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248011, d249107, d250255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248012 q = 1) (hb : d249108 q = 1) : d250256 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248012, d249108, d250256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248012, d249108, d250256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62634 (p : Pattern) (ha : d248018 p = 1) (hb : d249114 p = 1) : d250262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d247814 q = 1) (hb : d248904 q = 1) : d250082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247814, d248904, d250082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247814, d248904, d250082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62591 q ha hb
  have h2 (q : Pattern) (ha : d247815 q = 1) (hb : d248905 q = 1) : d250083 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247815, d248905, d250083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d247815, d248905, d250083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d247824 q = 1) (hb : d248914 q = 1) : d250092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247824, d248914, d250092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62591 q ha hb
    | true =>
      simp only [d247824, d248914, d250092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62594 q ha hb
  have h4 (q : Pattern) (ha : d247825 q = 1) (hb : d248915 q = 1) : d250093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247825, d248915, d250093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d247825, d248915, d250093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d247826 q = 1) (hb : d248916 q = 1) : d250094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247826, d248916, d250094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d247826, d248916, d250094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d247902 q = 1) (hb : d248996 q = 1) : d250165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247902, d248996, d250165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62607 q ha hb
    | true =>
      simp only [d247902, d248996, d250165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62614 q ha hb
  have h7 (q : Pattern) (ha : d247915 q = 1) (hb : d249009 q = 1) : d250178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247915, d249009, d250178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62615 q ha hb
    | true =>
      simp only [d247915, d249009, d250178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62616 q ha hb
  have h8 (q : Pattern) (ha : d247916 q = 1) (hb : d249010 q = 1) : d250179 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247916, d249010, d250179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d247916, d249010, d250179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d247917 q = 1) (hb : d249011 q = 1) : d250180 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247917, d249011, d250180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d247917, d249011, d250180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d247918 q = 1) (hb : d249012 q = 1) : d250181 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247918, d249012, d250181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d247918, d249012, d250181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d247922 q = 1) (hb : d249016 q = 1) : d250185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247922, d249016, d250185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247922, d249016, d250185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62617 q ha hb
  have h12 (q : Pattern) (ha : d247924 q = 1) (hb : d249018 q = 1) : d250187 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d247924, d249018, d250187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d247924, d249018, d250187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62618 q ha hb
  have h13 (q : Pattern) (ha : d247925 q = 1) (hb : d249019 q = 1) : d250188 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d247925, d249019, d250188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d247925, d249019, d250188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d247926 q = 1) (hb : d249020 q = 1) : d250189 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d247926, d249020, d250189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d247926, d249020, d250189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d247927 q = 1) (hb : d249021 q = 1) : d250190 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d247927, d249021, d250190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d247927, d249021, d250190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d247928 q = 1) (hb : d249022 q = 1) : d250191 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d247928, d249022, d250191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d247928, d249022, d250191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248006 q = 1) (hb : d249098 q = 1) : d250246 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248006, d249098, d250246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248006, d249098, d250246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62631 q ha hb
  have h18 (q : Pattern) (ha : d248013 q = 1) (hb : d249109 q = 1) : d250257 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248013, d249109, d250257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248013, d249109, d250257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62633 q ha hb
  have h19 (q : Pattern) (ha : d248014 q = 1) (hb : d249110 q = 1) : d250258 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248014, d249110, d250258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248014, d249110, d250258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d248015 q = 1) (hb : d249111 q = 1) : d250259 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248015, d249111, d250259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d248015, d249111, d250259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d248016 q = 1) (hb : d249112 q = 1) : d250260 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248016, d249112, d250260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d248016, d249112, d250260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d248017 q = 1) (hb : d249113 q = 1) : d250261 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248017, d249113, d250261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d248017, d249113, d250261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d248018 q = 1) (hb : d249114 q = 1) : d250262 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248018, d249114, d250262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248018, d249114, d250262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62635 (p : Pattern) (ha : d248024 p = 1) (hb : d249120 p = 1) : d250268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248019 q = 1) (hb : d249115 q = 1) : d250263 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248019, d249115, d250263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248019, d249115, d250263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62634 q ha hb
  have h2 (q : Pattern) (ha : d248020 q = 1) (hb : d249116 q = 1) : d250264 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248020, d249116, d250264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248020, d249116, d250264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248021 q = 1) (hb : d249117 q = 1) : d250265 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248021, d249117, d250265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248021, d249117, d250265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248022 q = 1) (hb : d249118 q = 1) : d250266 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248022, d249118, d250266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248022, d249118, d250266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248023 q = 1) (hb : d249119 q = 1) : d250267 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248023, d249119, d250267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248023, d249119, d250267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248024 q = 1) (hb : d249120 q = 1) : d250268 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248024, d249120, d250268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248024, d249120, d250268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62636 (p : Pattern) (ha : d101480 p = 1) (hb : d249124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h4 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d10052 q = 1) (hb : d101479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10053 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d101480 q = 1) (hb : d249124 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62637 (p : Pattern) (ha : d101510 p = 1) (hb : d249129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101485 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26558 q = 1) (hb : d101507 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26558, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d26559 q = 1) (hb : d101509 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26559, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26559, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d26560 q = 1) (hb : d101510 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26560, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26560, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d101510 q = 1) (hb : d249129 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62638 (p : Pattern) (ha : d248036 p = 1) (hb : d249135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248028 q = 1) (hb : d249125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
    | true =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248029 q = 1) (hb : d249126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248030 q = 1) (hb : d249127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248030, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248030, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248031 q = 1) (hb : d249128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248031, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248031, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248032 q = 1) (hb : d249130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
    | true =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248033 q = 1) (hb : d249131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248034 q = 1) (hb : d249132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248034, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248034, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248035 q = 1) (hb : d249133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248035, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248035, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248036 q = 1) (hb : d249134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248036, d249134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248036, d249134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d248036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d248036 q = 1) (hb : d249135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d249135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62639 (p : Pattern) (ha : d25764 p = 1) (hb : d52989 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309 q = 1) (hb : d52108 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, d52108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1520 q = 1) (hb : d52961 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d52961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1520, d52961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1532 q = 1) (hb : d52973 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1532, d52973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1532, d52973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d25764 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d25764, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25764, d52989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62640 (p : Pattern) (ha : d101510 p = 1) (hb : d249136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101485 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26558 q = 1) (hb : d101507 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26558, d101507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d25767 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d26581 q = 1) (hb : d101509 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26581, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26581, d101509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26582 q = 1) (hb : d101510 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26582, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26582, d101510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d101510 q = 1) (hb : d249136 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro62641 (p : Pattern) (ha : d248037 p = 1) (hb : d249147 p = 1) : d250273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248032 q = 1) (hb : d249137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62640 q ha hb
    | true =>
      simp only [d248032, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248033 q = 1) (hb : d249138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248033, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248034 q = 1) (hb : d249139 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248034, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248034, d249139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248035 q = 1) (hb : d249140 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248035, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248035, d249140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d249145 q = 1) : d249145 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d248037 q = 1) (hb : d249146 q = 1) : d250272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248037, d249146, d250272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248037, d249146, d250272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d248037 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d248037 q = 1) (hb : d249147 q = 1) : d250273 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249147, d250273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d249147, d250273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62642 (p : Pattern) (ha : d101560 p = 1) (hb : d249141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101560 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1575 q = 1) (hb : d53016 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h3 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h4 (q : Pattern) (ha : d1576 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1593 q = 1) (hb : d53034 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1593, d53034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10132 q = 1) (hb : d101559 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10132, d101559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10133 q = 1) (hb : d101560 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10133, d101560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d101560 q = 1) (hb : d249141 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro62643 (p : Pattern) (ha : d248045 p = 1) (hb : d249152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248041 q = 1) (hb : d249142 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248041, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62642 q ha hb
    | true =>
      simp only [d248041, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248042 q = 1) (hb : d249143 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248042, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248042, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248043 q = 1) (hb : d249144 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248043, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248043, d249144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248044 q = 1) (hb : d249145 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248044, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248044, d249145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248045 q = 1) (hb : d249151 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248045, d249151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248045, d249151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d248045 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248045 q = 1) (hb : d249152 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d249152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62644 (p : Pattern) (ha : d248052 p = 1) (hb : d249159 p = 1) : d250283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248038 q = 1) (hb : d249148 q = 1) : d250274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62638 q ha hb
    | true =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
  have h2 (q : Pattern) (ha : d248039 q = 1) (hb : d249149 q = 1) : d250275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248040 q = 1) (hb : d249150 q = 1) : d250276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248046 q = 1) (hb : d249153 q = 1) : d250277 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
    | true =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62643 q ha hb
  have h5 (q : Pattern) (ha : d248047 q = 1) (hb : d249154 q = 1) : d250278 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248048 q = 1) (hb : d249155 q = 1) : d250279 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248049 q = 1) (hb : d249156 q = 1) : d250280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248050 q = 1) (hb : d249157 q = 1) : d250281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248050, d249157, d250281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248050, d249157, d250281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248051 q = 1) (hb : d249158 q = 1) : d250282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248051, d249158, d250282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248051, d249158, d250282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248052 q = 1) (hb : d249159 q = 1) : d250283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248052, d249159, d250283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248052, d249159, d250283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62645 (p : Pattern) (ha : d248056 p = 1) (hb : d249163 p = 1) : d250287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248046 q = 1) (hb : d249153 q = 1) : d250277 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
    | true =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62643 q ha hb
  have h2 (q : Pattern) (ha : d248047 q = 1) (hb : d249154 q = 1) : d250278 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248048 q = 1) (hb : d249155 q = 1) : d250279 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248050 q = 1) (hb : d249157 q = 1) : d250281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248050, d249157, d250281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248050, d249157, d250281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248055 q = 1) (hb : d249162 q = 1) : d250286 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248055, d249162, d250286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248055, d249162, d250286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248056 q = 1) (hb : d249163 q = 1) : d250287 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248056, d249163, d250287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248056, d249163, d250287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62646 (p : Pattern) (ha : d248062 p = 1) (hb : d249169 p = 1) : d250293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248060 q = 1) (hb : d249167 q = 1) : d250291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248061 q = 1) (hb : d249168 q = 1) : d250292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248061, d249168, d250292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248061, d249168, d250292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248062 q = 1) (hb : d249169 q = 1) : d250293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248062, d249169, d250293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248062, d249169, d250293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62647 (p : Pattern) (ha : d248066 p = 1) (hb : d249173 p = 1) : d250297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248064 q = 1) (hb : d249171 q = 1) : d250295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248065 q = 1) (hb : d249172 q = 1) : d250296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248065, d249172, d250296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248065, d249172, d250296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248066 q = 1) (hb : d249173 q = 1) : d250297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248066, d249173, d250297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248066, d249173, d250297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62648 (p : Pattern) (ha : d248072 p = 1) (hb : d249179 p = 1) : d250303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248067 q = 1) (hb : d249174 q = 1) : d250298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
    | true =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
  have h2 (q : Pattern) (ha : d248068 q = 1) (hb : d249175 q = 1) : d250299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248069 q = 1) (hb : d249176 q = 1) : d250300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248070 q = 1) (hb : d249177 q = 1) : d250301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248071 q = 1) (hb : d249178 q = 1) : d250302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248072 q = 1) (hb : d249179 q = 1) : d250303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248072, d249179, d250303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248072, d249179, d250303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62649 (p : Pattern) (ha : d248075 p = 1) (hb : d249182 p = 1) : d250306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248060 q = 1) (hb : d249167 q = 1) : d250291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248061 q = 1) (hb : d249168 q = 1) : d250292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248061, d249168, d250292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248061, d249168, d250292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248075 q = 1) (hb : d249182 q = 1) : d250306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248075, d249182, d250306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248075, d249182, d250306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62650 (p : Pattern) (ha : d248076 p = 1) (hb : d249183 p = 1) : d250307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248064 q = 1) (hb : d249171 q = 1) : d250295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248065 q = 1) (hb : d249172 q = 1) : d250296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248065, d249172, d250296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248065, d249172, d250296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248076 q = 1) (hb : d249183 q = 1) : d250307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248076, d249183, d250307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248076, d249183, d250307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62651 (p : Pattern) (ha : d248082 p = 1) (hb : d249189 p = 1) : d250313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248067 q = 1) (hb : d249174 q = 1) : d250298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
    | true =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
  have h2 (q : Pattern) (ha : d248068 q = 1) (hb : d249175 q = 1) : d250299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248069 q = 1) (hb : d249176 q = 1) : d250300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248070 q = 1) (hb : d249177 q = 1) : d250301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248071 q = 1) (hb : d249178 q = 1) : d250302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248077 q = 1) (hb : d249184 q = 1) : d250308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62649 q ha hb
    | true =>
      simp only [d248077, d249184, d250308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62650 q ha hb
  have h7 (q : Pattern) (ha : d248078 q = 1) (hb : d249185 q = 1) : d250309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248078, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248078, d249185, d250309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248079 q = 1) (hb : d249186 q = 1) : d250310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248079, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248079, d249186, d250310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248080 q = 1) (hb : d249187 q = 1) : d250311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248080, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248080, d249187, d250311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248081 q = 1) (hb : d249188 q = 1) : d250312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248081, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248081, d249188, d250312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248082 q = 1) (hb : d249189 q = 1) : d250313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248082, d249189, d250313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248082, d249189, d250313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62652 (p : Pattern) (ha : d248087 p = 1) (hb : d249194 p = 1) : d250318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248060 q = 1) (hb : d249167 q = 1) : d250291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248086 q = 1) (hb : d249193 q = 1) : d250317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248086, d249193, d250317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248086, d249193, d250317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248087 q = 1) (hb : d249194 q = 1) : d250318 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248087, d249194, d250318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248087, d249194, d250318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62653 (p : Pattern) (ha : d248089 p = 1) (hb : d249196 p = 1) : d250320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248064 q = 1) (hb : d249171 q = 1) : d250295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248088 q = 1) (hb : d249195 q = 1) : d250319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248088, d249195, d250319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248088, d249195, d250319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248089 q = 1) (hb : d249196 q = 1) : d250320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248089, d249196, d250320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248089, d249196, d250320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62654 (p : Pattern) (ha : d248096 p = 1) (hb : d249203 p = 1) : d250327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248094 q = 1) (hb : d249201 q = 1) : d250325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248094, d249201, d250325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248094, d249201, d250325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248095 q = 1) (hb : d249202 q = 1) : d250326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248095, d249202, d250326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248095, d249202, d250326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248096 q = 1) (hb : d249203 q = 1) : d250327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248096, d249203, d250327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248096, d249203, d250327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62655 (p : Pattern) (ha : d248099 p = 1) (hb : d249206 p = 1) : d250330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248097 q = 1) (hb : d249204 q = 1) : d250328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248097, d249204, d250328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248097, d249204, d250328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248098 q = 1) (hb : d249205 q = 1) : d250329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248098, d249205, d250329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248098, d249205, d250329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248099 q = 1) (hb : d249206 q = 1) : d250330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248099, d249206, d250330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248099, d249206, d250330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62656 (p : Pattern) (ha : d248037 p = 1) (hb : d249216 p = 1) : d250273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248032 q = 1) (hb : d249130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
    | true =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248033 q = 1) (hb : d249131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248034 q = 1) (hb : d249132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248034, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248034, d249132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248035 q = 1) (hb : d249133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248035, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248035, d249133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d249145 q = 1) : d249145 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d248037 q = 1) (hb : d249215 q = 1) : d250272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248037, d249215, d250272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248037, d249215, d250272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d248037 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d248037 q = 1) (hb : d249216 q = 1) : d250273 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249216, d250273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d249216, d250273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62657 (p : Pattern) (ha : d26652 p = 1) (hb : d101471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10042 q = 1) (hb : d101469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10042, d101469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10043 q = 1) (hb : d101470 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10043, d101470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10044 q = 1) (hb : d101471 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10044, d101471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d26652 q = 1) (hb : d101471 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62658 (p : Pattern) (ha : d248107 p = 1) (hb : d249211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26653 q = 1) (hb : d248103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d248103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62657 q ha hb
    | true =>
      simp only [d26653, d248103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26654 q = 1) (hb : d248104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d248104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26654, d248104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26655 q = 1) (hb : d248105 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26655, d248105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26655, d248105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26656 q = 1) (hb : d248106 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26656, d248106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26656, d248106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d248028 q = 1) (hb : d249125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
    | true =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248029 q = 1) (hb : d249126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248030 q = 1) (hb : d249127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248030, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248030, d249127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248031 q = 1) (hb : d249128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248031, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248031, d249128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248107 q = 1) (hb : d249210 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248107, d249210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248107, d249210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d248107 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d248107 q = 1) (hb : d249211 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d249211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62659 (p : Pattern) (ha : d248113 p = 1) (hb : d249222 p = 1) : d250336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248108 q = 1) (hb : d249212 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248108, d249212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62658 q ha hb
    | true =>
      simp only [d248108, d249212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62638 q ha hb
  have h2 (q : Pattern) (ha : d248109 q = 1) (hb : d249213 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248109, d249213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248109, d249213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248110 q = 1) (hb : d249214 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248110, d249214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248110, d249214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248038 q = 1) (hb : d249217 q = 1) : d250274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248038, d249217, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62638 q ha hb
    | true =>
      simp only [d248038, d249217, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62656 q ha hb
  have h5 (q : Pattern) (ha : d248039 q = 1) (hb : d249218 q = 1) : d250275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248039, d249218, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248039, d249218, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248040 q = 1) (hb : d249219 q = 1) : d250276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248040, d249219, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248040, d249219, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248111 q = 1) (hb : d249220 q = 1) : d250334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248111, d249220, d250334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248111, d249220, d250334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248038 q = 1) (hb : d249148 q = 1) : d250274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62638 q ha hb
    | true =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
  have h9 (q : Pattern) (ha : d248039 q = 1) (hb : d249149 q = 1) : d250275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248040 q = 1) (hb : d249150 q = 1) : d250276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248046 q = 1) (hb : d249153 q = 1) : d250277 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
    | true =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62643 q ha hb
  have h12 (q : Pattern) (ha : d248047 q = 1) (hb : d249154 q = 1) : d250278 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248048 q = 1) (hb : d249155 q = 1) : d250279 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248049 q = 1) (hb : d249156 q = 1) : d250280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248112 q = 1) (hb : d249221 q = 1) : d250335 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248112, d249221, d250335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248112, d249221, d250335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248113 q = 1) (hb : d249222 q = 1) : d250336 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248113, d249222, d250336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248113, d249222, d250336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62660 (p : Pattern) (ha : d248119 p = 1) (hb : d249228 p = 1) : d250342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248114 q = 1) (hb : d249223 q = 1) : d250337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248114, d249223, d250337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62659 q ha hb
    | true =>
      simp only [d248114, d249223, d250337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248115 q = 1) (hb : d249224 q = 1) : d250338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248115, d249224, d250338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248115, d249224, d250338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248116 q = 1) (hb : d249225 q = 1) : d250339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248116, d249225, d250339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248116, d249225, d250339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248117 q = 1) (hb : d249226 q = 1) : d250340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248117, d249226, d250340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248117, d249226, d250340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248118 q = 1) (hb : d249227 q = 1) : d250341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248118, d249227, d250341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248118, d249227, d250341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248119 q = 1) (hb : d249228 q = 1) : d250342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248119, d249228, d250342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248119, d249228, d250342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62661 (p : Pattern) (ha : d248127 p = 1) (hb : d249236 p = 1) : d250350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248038 q = 1) (hb : d249148 q = 1) : d250274 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62638 q ha hb
    | true =>
      simp only [d248038, d249148, d250274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
  have h2 (q : Pattern) (ha : d248039 q = 1) (hb : d249149 q = 1) : d250275 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248039, d249149, d250275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248040 q = 1) (hb : d249150 q = 1) : d250276 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248040, d249150, d250276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248046 q = 1) (hb : d249153 q = 1) : d250277 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
    | true =>
      simp only [d248046, d249153, d250277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62643 q ha hb
  have h5 (q : Pattern) (ha : d248047 q = 1) (hb : d249154 q = 1) : d250278 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248047, d249154, d250278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248048 q = 1) (hb : d249155 q = 1) : d250279 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248048, d249155, d250279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248049 q = 1) (hb : d249156 q = 1) : d250280 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248049, d249156, d250280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157418 q = 1) : d157418 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d248122 q = 1) (hb : d249231 q = 1) : d250345 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248122, d249231, d250345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62641 q ha hb
    | true =>
      simp only [d248122, d249231, d250345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248123 q = 1) (hb : d249232 q = 1) : d250346 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248123, d249232, d250346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248123, d249232, d250346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248124 q = 1) (hb : d249233 q = 1) : d250347 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248124, d249233, d250347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248124, d249233, d250347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248125 q = 1) (hb : d249234 q = 1) : d250348 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248125, d249234, d250348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248125, d249234, d250348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248126 q = 1) (hb : d249235 q = 1) : d250349 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248126, d249235, d250349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248126, d249235, d250349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248127 q = 1) (hb : d249236 q = 1) : d250350 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248127, d249236, d250350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248127, d249236, d250350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62662 (p : Pattern) (ha : d248133 p = 1) (hb : d249242 p = 1) : d250356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248128 q = 1) (hb : d249237 q = 1) : d250351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248128, d249237, d250351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62661 q ha hb
    | true =>
      simp only [d248128, d249237, d250351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248129 q = 1) (hb : d249238 q = 1) : d250352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248129, d249238, d250352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248129, d249238, d250352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248130 q = 1) (hb : d249239 q = 1) : d250353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248130, d249239, d250353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248130, d249239, d250353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248131 q = 1) (hb : d249240 q = 1) : d250354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248131, d249240, d250354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248131, d249240, d250354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248132 q = 1) (hb : d249241 q = 1) : d250355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248132, d249241, d250355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248132, d249241, d250355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248133 q = 1) (hb : d249242 q = 1) : d250356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248133, d249242, d250356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248133, d249242, d250356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62663 (p : Pattern) (ha : d248139 p = 1) (hb : d249248 p = 1) : d250362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248090 q = 1) (hb : d249197 q = 1) : d250321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248090, d249197, d250321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62652 q ha hb
    | true =>
      simp only [d248090, d249197, d250321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62653 q ha hb
  have h2 (q : Pattern) (ha : d248091 q = 1) (hb : d249198 q = 1) : d250322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248091, d249198, d250322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248091, d249198, d250322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248092 q = 1) (hb : d249199 q = 1) : d250323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248092, d249199, d250323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248092, d249199, d250323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248093 q = 1) (hb : d249200 q = 1) : d250324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248093, d249200, d250324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248093, d249200, d250324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248100 q = 1) (hb : d249207 q = 1) : d250331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248100, d249207, d250331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62654 q ha hb
    | true =>
      simp only [d248100, d249207, d250331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62655 q ha hb
  have h6 (q : Pattern) (ha : d248101 q = 1) (hb : d249208 q = 1) : d250332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248101, d249208, d250332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248101, d249208, d250332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248102 q = 1) (hb : d249209 q = 1) : d250333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248102, d249209, d250333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248102, d249209, d250333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248120 q = 1) (hb : d249229 q = 1) : d250343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248120, d249229, d250343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62660 q ha hb
    | true =>
      simp only [d248120, d249229, d250343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248067 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248121 q = 1) (hb : d249230 q = 1) : d250344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248121, d249230, d250344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248121, d249230, d250344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d248134 q = 1) (hb : d249243 q = 1) : d250357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248134, d249243, d250357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62662 q ha hb
    | true =>
      simp only [d248134, d249243, d250357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d248135 q = 1) (hb : d249244 q = 1) : d250358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248135, d249244, d250358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248135, d249244, d250358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248136 q = 1) (hb : d249245 q = 1) : d250359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248136, d249245, d250359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248136, d249245, d250359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248137 q = 1) (hb : d249246 q = 1) : d250360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248137, d249246, d250360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248137, d249246, d250360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248138 q = 1) (hb : d249247 q = 1) : d250361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248138, d249247, d250361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248138, d249247, d250361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248139 q = 1) (hb : d249248 q = 1) : d250362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248139, d249248, d250362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248139, d249248, d250362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62664 (p : Pattern) (ha : d248140 p = 1) (hb : d249249 p = 1) : d250363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248060 q = 1) (hb : d249167 q = 1) : d250291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248060, d249167, d250291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248086 q = 1) (hb : d249193 q = 1) : d250317 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248086, d249193, d250317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248086, d249193, d250317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248140 q = 1) (hb : d249249 q = 1) : d250363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248140, d249249, d250363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248140, d249249, d250363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62665 (p : Pattern) (ha : d248141 p = 1) (hb : d249250 p = 1) : d250364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248064 q = 1) (hb : d249171 q = 1) : d250295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248064, d249171, d250295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248088 q = 1) (hb : d249195 q = 1) : d250319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248088, d249195, d250319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248088, d249195, d250319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248141 q = 1) (hb : d249250 q = 1) : d250364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248141, d249250, d250364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248141, d249250, d250364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62666 (p : Pattern) (ha : d248146 p = 1) (hb : d249255 p = 1) : d250369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248059 q = 1) (hb : d249166 q = 1) : d250290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248059, d249166, d250290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248094 q = 1) (hb : d249201 q = 1) : d250325 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248094, d249201, d250325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248094, d249201, d250325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248095 q = 1) (hb : d249202 q = 1) : d250326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248095, d249202, d250326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248095, d249202, d250326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248146 q = 1) (hb : d249255 q = 1) : d250369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248146, d249255, d250369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248146, d249255, d250369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62667 (p : Pattern) (ha : d248147 p = 1) (hb : d249256 p = 1) : d250370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248057 q = 1) (hb : d249164 q = 1) : d250288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62645 q ha hb
    | true =>
      simp only [d248057, d249164, d250288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248058 q = 1) (hb : d249165 q = 1) : d250289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248058, d249165, d250289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248063 q = 1) (hb : d249170 q = 1) : d250294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248063, d249170, d250294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248097 q = 1) (hb : d249204 q = 1) : d250328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248097, d249204, d250328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248097, d249204, d250328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248098 q = 1) (hb : d249205 q = 1) : d250329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248098, d249205, d250329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248098, d249205, d250329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248147 q = 1) (hb : d249256 q = 1) : d250370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248147, d249256, d250370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248147, d249256, d250370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62668 (p : Pattern) (ha : d248151 p = 1) (hb : d249260 p = 1) : d250374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248114 q = 1) (hb : d249223 q = 1) : d250337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248114, d249223, d250337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62659 q ha hb
    | true =>
      simp only [d248114, d249223, d250337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248115 q = 1) (hb : d249224 q = 1) : d250338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248115, d249224, d250338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248115, d249224, d250338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248053 q = 1) (hb : d249160 q = 1) : d250284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62644 q ha hb
    | true =>
      simp only [d248053, d249160, d250284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248054 q = 1) (hb : d249161 q = 1) : d250285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248054, d249161, d250285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248116 q = 1) (hb : d249225 q = 1) : d250339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248116, d249225, d250339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248116, d249225, d250339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248117 q = 1) (hb : d249226 q = 1) : d250340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248117, d249226, d250340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248117, d249226, d250340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248118 q = 1) (hb : d249227 q = 1) : d250341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248118, d249227, d250341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248118, d249227, d250341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248151 q = 1) (hb : d249260 q = 1) : d250374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248151, d249260, d250374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248151, d249260, d250374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62669 (p : Pattern) (ha : d248154 p = 1) (hb : d249263 p = 1) : d250377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248128 q = 1) (hb : d249237 q = 1) : d250351 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248128, d249237, d250351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62661 q ha hb
    | true =>
      simp only [d248128, d249237, d250351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248129 q = 1) (hb : d249238 q = 1) : d250352 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248129, d249238, d250352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248129, d249238, d250352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248130 q = 1) (hb : d249239 q = 1) : d250353 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248130, d249239, d250353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248130, d249239, d250353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248131 q = 1) (hb : d249240 q = 1) : d250354 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248131, d249240, d250354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248131, d249240, d250354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248132 q = 1) (hb : d249241 q = 1) : d250355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248132, d249241, d250355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248132, d249241, d250355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248154 q = 1) (hb : d249263 q = 1) : d250377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248154, d249263, d250377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248154, d249263, d250377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62670 (p : Pattern) (ha : d248160 p = 1) (hb : d249269 p = 1) : d250383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248090 q = 1) (hb : d249197 q = 1) : d250321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248090, d249197, d250321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62652 q ha hb
    | true =>
      simp only [d248090, d249197, d250321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62653 q ha hb
  have h2 (q : Pattern) (ha : d248091 q = 1) (hb : d249198 q = 1) : d250322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248091, d249198, d250322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248091, d249198, d250322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248092 q = 1) (hb : d249199 q = 1) : d250323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248092, d249199, d250323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248092, d249199, d250323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248093 q = 1) (hb : d249200 q = 1) : d250324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248093, d249200, d250324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248093, d249200, d250324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248100 q = 1) (hb : d249207 q = 1) : d250331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248100, d249207, d250331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62654 q ha hb
    | true =>
      simp only [d248100, d249207, d250331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62655 q ha hb
  have h6 (q : Pattern) (ha : d248101 q = 1) (hb : d249208 q = 1) : d250332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248101, d249208, d250332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248101, d249208, d250332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248102 q = 1) (hb : d249209 q = 1) : d250333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248102, d249209, d250333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248102, d249209, d250333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248120 q = 1) (hb : d249229 q = 1) : d250343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248120, d249229, d250343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62660 q ha hb
    | true =>
      simp only [d248120, d249229, d250343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248067 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248121 q = 1) (hb : d249230 q = 1) : d250344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248121, d249230, d250344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248121, d249230, d250344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d248134 q = 1) (hb : d249243 q = 1) : d250357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248134, d249243, d250357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62662 q ha hb
    | true =>
      simp only [d248134, d249243, d250357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d248135 q = 1) (hb : d249244 q = 1) : d250358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248135, d249244, d250358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248135, d249244, d250358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248136 q = 1) (hb : d249245 q = 1) : d250359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248136, d249245, d250359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248136, d249245, d250359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248137 q = 1) (hb : d249246 q = 1) : d250360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248137, d249246, d250360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248137, d249246, d250360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248138 q = 1) (hb : d249247 q = 1) : d250361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248138, d249247, d250361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248138, d249247, d250361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248142 q = 1) (hb : d249251 q = 1) : d250365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248142, d249251, d250365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62664 q ha hb
    | true =>
      simp only [d248142, d249251, d250365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62665 q ha hb
  have h17 (q : Pattern) (ha : d248143 q = 1) (hb : d249252 q = 1) : d250366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248143, d249252, d250366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248143, d249252, d250366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248144 q = 1) (hb : d249253 q = 1) : d250367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248144, d249253, d250367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248144, d249253, d250367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d248145 q = 1) (hb : d249254 q = 1) : d250368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248145, d249254, d250368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248145, d249254, d250368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d248148 q = 1) (hb : d249257 q = 1) : d250371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248148, d249257, d250371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62666 q ha hb
    | true =>
      simp only [d248148, d249257, d250371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62667 q ha hb
  have h21 (q : Pattern) (ha : d248149 q = 1) (hb : d249258 q = 1) : d250372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248149, d249258, d250372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248149, d249258, d250372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d248150 q = 1) (hb : d249259 q = 1) : d250373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248150, d249259, d250373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d248150, d249259, d250373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d248152 q = 1) (hb : d249261 q = 1) : d250375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248152, d249261, d250375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62668 q ha hb
    | true =>
      simp only [d248152, d249261, d250375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62649 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d248077 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d248153 q = 1) (hb : d249262 q = 1) : d250376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248153, d249262, d250376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d248153, d249262, d250376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d248155 q = 1) (hb : d249264 q = 1) : d250378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248155, d249264, d250378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62669 q ha hb
    | true =>
      simp only [d248155, d249264, d250378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d248156 q = 1) (hb : d249265 q = 1) : d250379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248156, d249265, d250379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d248156, d249265, d250379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d248157 q = 1) (hb : d249266 q = 1) : d250380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248157, d249266, d250380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d248157, d249266, d250380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d248158 q = 1) (hb : d249267 q = 1) : d250381 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248158, d249267, d250381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d248158, d249267, d250381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d248159 q = 1) (hb : d249268 q = 1) : d250382 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248159, d249268, d250382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d248159, d249268, d250382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d248160 q = 1) (hb : d249269 q = 1) : d250383 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248160, d249269, d250383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248160, d249269, d250383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62671 (p : Pattern) (ha : d248167 p = 1) (hb : d249276 p = 1) : d250390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248067 q = 1) (hb : d249174 q = 1) : d250298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62646 q ha hb
    | true =>
      simp only [d248067, d249174, d250298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
  have h2 (q : Pattern) (ha : d248068 q = 1) (hb : d249175 q = 1) : d250299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248068, d249175, d250299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248069 q = 1) (hb : d249176 q = 1) : d250300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248069, d249176, d250300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248070 q = 1) (hb : d249177 q = 1) : d250301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248070, d249177, d250301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248071 q = 1) (hb : d249178 q = 1) : d250302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248071, d249178, d250302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248162 q = 1) (hb : d249271 q = 1) : d250385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248162, d249271, d250385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
    | true =>
      simp only [d248162, d249271, d250385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248163 q = 1) (hb : d249272 q = 1) : d250386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248163, d249272, d250386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248163, d249272, d250386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248164 q = 1) (hb : d249273 q = 1) : d250387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248164, d249273, d250387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248164, d249273, d250387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248165 q = 1) (hb : d249274 q = 1) : d250388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248165, d249274, d250388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248165, d249274, d250388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248166 q = 1) (hb : d249275 q = 1) : d250389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248166, d249275, d250389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248166, d249275, d250389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248167 q = 1) (hb : d249276 q = 1) : d250390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248167, d249276, d250390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248167, d249276, d250390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62672 (p : Pattern) (ha : d248173 p = 1) (hb : d249282 p = 1) : d250396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248162 q = 1) (hb : d249271 q = 1) : d250385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248162, d249271, d250385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62647 q ha hb
    | true =>
      simp only [d248162, d249271, d250385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248163 q = 1) (hb : d249272 q = 1) : d250386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248163, d249272, d250386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248163, d249272, d250386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248164 q = 1) (hb : d249273 q = 1) : d250387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248164, d249273, d250387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248164, d249273, d250387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248165 q = 1) (hb : d249274 q = 1) : d250388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248165, d249274, d250388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248165, d249274, d250388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248166 q = 1) (hb : d249275 q = 1) : d250389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248166, d249275, d250389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248166, d249275, d250389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248168 q = 1) (hb : d249277 q = 1) : d250391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248168, d249277, d250391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62650 q ha hb
    | true =>
      simp only [d248168, d249277, d250391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248169 q = 1) (hb : d249278 q = 1) : d250392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248169, d249278, d250392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248169, d249278, d250392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248170 q = 1) (hb : d249279 q = 1) : d250393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248170, d249279, d250393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248170, d249279, d250393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248171 q = 1) (hb : d249280 q = 1) : d250394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248171, d249280, d250394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248171, d249280, d250394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248172 q = 1) (hb : d249281 q = 1) : d250395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248172, d249281, d250395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248172, d249281, d250395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248173 q = 1) (hb : d249282 q = 1) : d250396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248173, d249282, d250396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248173, d249282, d250396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62673 (p : Pattern) (ha : d248180 p = 1) (hb : d249289 p = 1) : d250403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248152 q = 1) (hb : d249261 q = 1) : d250375 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248152, d249261, d250375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62668 q ha hb
    | true =>
      simp only [d248152, d249261, d250375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62649 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248077 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248153 q = 1) (hb : d249262 q = 1) : d250376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248153, d249262, d250376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248153, d249262, d250376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d248155 q = 1) (hb : d249264 q = 1) : d250378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248155, d249264, d250378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62669 q ha hb
    | true =>
      simp only [d248155, d249264, d250378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248156 q = 1) (hb : d249265 q = 1) : d250379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248156, d249265, d250379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248156, d249265, d250379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248157 q = 1) (hb : d249266 q = 1) : d250380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248157, d249266, d250380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248157, d249266, d250380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248178 q = 1) (hb : d249287 q = 1) : d250401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248178, d249287, d250401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248178, d249287, d250401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248179 q = 1) (hb : d249288 q = 1) : d250402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248179, d249288, d250402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248179, d249288, d250402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248180 q = 1) (hb : d249289 q = 1) : d250403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248180, d249289, d250403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248180, d249289, d250403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62674 (p : Pattern) (ha : d248182 p = 1) (hb : d249291 p = 1) : d250405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248168 q = 1) (hb : d249277 q = 1) : d250391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248168, d249277, d250391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62650 q ha hb
    | true =>
      simp only [d248168, d249277, d250391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248169 q = 1) (hb : d249278 q = 1) : d250392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248169, d249278, d250392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248169, d249278, d250392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248170 q = 1) (hb : d249279 q = 1) : d250393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248170, d249279, d250393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248170, d249279, d250393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248171 q = 1) (hb : d249280 q = 1) : d250394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248171, d249280, d250394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248171, d249280, d250394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248172 q = 1) (hb : d249281 q = 1) : d250395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248172, d249281, d250395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248172, d249281, d250395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248182 q = 1) (hb : d249291 q = 1) : d250405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248182, d249291, d250405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248182, d249291, d250405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62675 (p : Pattern) (ha : d248196 p = 1) (hb : d249302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26834 q = 1) (hb : d248188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26834, d248188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26834, d248188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62657 q ha hb
  have h2 (q : Pattern) (ha : d26653 q = 1) (hb : d248103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d248103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62657 q ha hb
    | true =>
      simp only [d26653, d248103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26835 q = 1) (hb : d248189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26835, d248189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26835, d248189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26654 q = 1) (hb : d248104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d248104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26654, d248104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26836 q = 1) (hb : d248190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26836, d248190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26836, d248190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26837 q = 1) (hb : d248191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26837, d248191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26837, d248191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d248192 q = 1) (hb : d249297 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248192, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248192, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
  have h8 (q : Pattern) (ha : d248028 q = 1) (hb : d249125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
    | true =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248193 q = 1) (hb : d249298 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248193, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248193, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248029 q = 1) (hb : d249126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d248194 q = 1) (hb : d249299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248194, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248194, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248195 q = 1) (hb : d249300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248195, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248195, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248196 q = 1) (hb : d249301 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248196, d249301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d248196, d249301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248196 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248196 q = 1) (hb : d249302 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62676 (p : Pattern) (ha : d248201 p = 1) (hb : d249308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248192 q = 1) (hb : d249297 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248192, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248192, d249297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
  have h2 (q : Pattern) (ha : d248028 q = 1) (hb : d249125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62636 q ha hb
    | true =>
      simp only [d248028, d249125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248193 q = 1) (hb : d249298 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248193, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248193, d249298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248029 q = 1) (hb : d249126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248029, d249126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248194 q = 1) (hb : d249299 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248194, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248194, d249299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248195 q = 1) (hb : d249300 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248195, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248195, d249300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248197 q = 1) (hb : d249303 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248197, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248197, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
  have h8 (q : Pattern) (ha : d248032 q = 1) (hb : d249130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
    | true =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248198 q = 1) (hb : d249304 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248198, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248198, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248033 q = 1) (hb : d249131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d248199 q = 1) (hb : d249305 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248199, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248199, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248200 q = 1) (hb : d249306 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248200, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248200, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248201 q = 1) (hb : d249307 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248201, d249307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248201, d249307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248201 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248201 q = 1) (hb : d249308 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62677 (p : Pattern) (ha : d248205 p = 1) (hb : d249317 p = 1) : d250412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248197 q = 1) (hb : d249303 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248197, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248197, d249303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
  have h2 (q : Pattern) (ha : d248032 q = 1) (hb : d249130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62637 q ha hb
    | true =>
      simp only [d248032, d249130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248198 q = 1) (hb : d249304 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248198, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248198, d249304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248033 q = 1) (hb : d249131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248033, d249131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248199 q = 1) (hb : d249305 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248199, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248199, d249305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248200 q = 1) (hb : d249306 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248200, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248200, d249306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d249315 q = 1) : d249315 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d248205 q = 1) (hb : d249316 q = 1) : d250411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248205, d249316, d250411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248205, d249316, d250411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248205 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248205 q = 1) (hb : d249317 q = 1) : d250412 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249317, d250412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249317, d250412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62678 (p : Pattern) (ha : d248205 p = 1) (hb : d249327 p = 1) : d250412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248197 q = 1) (hb : d249322 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248197, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248197, d249322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62640 q ha hb
  have h2 (q : Pattern) (ha : d248032 q = 1) (hb : d249137 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248032, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62640 q ha hb
    | true =>
      simp only [d248032, d249137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248198 q = 1) (hb : d249323 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248198, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248198, d249323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248033 q = 1) (hb : d249138 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248033, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248033, d249138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248199 q = 1) (hb : d249324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248199, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248199, d249324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248200 q = 1) (hb : d249325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248200, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248200, d249325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d249315 q = 1) : d249315 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d248205 q = 1) (hb : d249326 q = 1) : d250411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248205, d249326, d250411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248205, d249326, d250411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248205 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248205 q = 1) (hb : d249327 q = 1) : d250412 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249327, d250412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249327, d250412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62679 (p : Pattern) (ha : d248214 p = 1) (hb : d249332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248210 q = 1) (hb : d249312 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248210, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248210, d249312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62642 q ha hb
  have h2 (q : Pattern) (ha : d248041 q = 1) (hb : d249142 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248041, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62642 q ha hb
    | true =>
      simp only [d248041, d249142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248211 q = 1) (hb : d249313 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248211, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248211, d249313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248042 q = 1) (hb : d249143 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248042, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248042, d249143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248212 q = 1) (hb : d249314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248212, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248212, d249314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248213 q = 1) (hb : d249315 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248213, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248213, d249315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248214 q = 1) (hb : d249331 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248214, d249331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248214, d249331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d248214 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d248214 q = 1) (hb : d249332 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d249332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62680 (p : Pattern) (ha : d248220 p = 1) (hb : d249338 p = 1) : d250422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248202 q = 1) (hb : d249309 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248202, d249309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62675 q ha hb
    | true =>
      simp only [d248202, d249309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62676 q ha hb
  have h2 (q : Pattern) (ha : d248203 q = 1) (hb : d249310 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248203, d249310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248203, d249310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248204 q = 1) (hb : d249311 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248204, d249311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248204, d249311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248206 q = 1) (hb : d249318 q = 1) : d250413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248206, d249318, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62676 q ha hb
    | true =>
      simp only [d248206, d249318, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62677 q ha hb
  have h5 (q : Pattern) (ha : d248207 q = 1) (hb : d249319 q = 1) : d250414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248207, d249319, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248207, d249319, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248208 q = 1) (hb : d249320 q = 1) : d250415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248208, d249320, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248208, d249320, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248209 q = 1) (hb : d249321 q = 1) : d250416 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248209, d249321, d250416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248209, d249321, d250416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248206 q = 1) (hb : d249328 q = 1) : d250413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62676 q ha hb
    | true =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
  have h9 (q : Pattern) (ha : d248207 q = 1) (hb : d249329 q = 1) : d250414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248208 q = 1) (hb : d249330 q = 1) : d250415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248215 q = 1) (hb : d249333 q = 1) : d250417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
    | true =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62679 q ha hb
  have h12 (q : Pattern) (ha : d248216 q = 1) (hb : d249334 q = 1) : d250418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248217 q = 1) (hb : d249335 q = 1) : d250419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248218 q = 1) (hb : d249336 q = 1) : d250420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248219 q = 1) (hb : d249337 q = 1) : d250421 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248219, d249337, d250421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248219, d249337, d250421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248220 q = 1) (hb : d249338 q = 1) : d250422 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248220, d249338, d250422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248220, d249338, d250422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62681 (p : Pattern) (ha : d248225 p = 1) (hb : d249343 p = 1) : d250427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248206 q = 1) (hb : d249328 q = 1) : d250413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62676 q ha hb
    | true =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
  have h2 (q : Pattern) (ha : d248207 q = 1) (hb : d249329 q = 1) : d250414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248208 q = 1) (hb : d249330 q = 1) : d250415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248215 q = 1) (hb : d249333 q = 1) : d250417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
    | true =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62679 q ha hb
  have h5 (q : Pattern) (ha : d248216 q = 1) (hb : d249334 q = 1) : d250418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248217 q = 1) (hb : d249335 q = 1) : d250419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248218 q = 1) (hb : d249336 q = 1) : d250420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248223 q = 1) (hb : d249341 q = 1) : d250425 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248223, d249341, d250425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248223, d249341, d250425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248224 q = 1) (hb : d249342 q = 1) : d250426 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248224, d249342, d250426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248224, d249342, d250426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248225 q = 1) (hb : d249343 q = 1) : d250427 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248225, d249343, d250427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248225, d249343, d250427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62682 (p : Pattern) (ha : d248231 p = 1) (hb : d249349 p = 1) : d250433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248221 q = 1) (hb : d249339 q = 1) : d250423 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248221, d249339, d250423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62680 q ha hb
    | true =>
      simp only [d248221, d249339, d250423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248222 q = 1) (hb : d249340 q = 1) : d250424 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248222, d249340, d250424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248222, d249340, d250424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248226 q = 1) (hb : d249344 q = 1) : d250428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248226, d249344, d250428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62681 q ha hb
    | true =>
      simp only [d248226, d249344, d250428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248227 q = 1) (hb : d249345 q = 1) : d250429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248227, d249345, d250429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248227, d249345, d250429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248228 q = 1) (hb : d249346 q = 1) : d250430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248228, d249346, d250430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248228, d249346, d250430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248229 q = 1) (hb : d249347 q = 1) : d250431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248229, d249347, d250431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248229, d249347, d250431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248230 q = 1) (hb : d249348 q = 1) : d250432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248230, d249348, d250432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248230, d249348, d250432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248231 q = 1) (hb : d249349 q = 1) : d250433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248231, d249349, d250433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248231, d249349, d250433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62683 (p : Pattern) (ha : d248233 p = 1) (hb : d249351 p = 1) : d250435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248215 q = 1) (hb : d249333 q = 1) : d250417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
    | true =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62679 q ha hb
  have h2 (q : Pattern) (ha : d248216 q = 1) (hb : d249334 q = 1) : d250418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248217 q = 1) (hb : d249335 q = 1) : d250419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248223 q = 1) (hb : d249341 q = 1) : d250425 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248223, d249341, d250425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248223, d249341, d250425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248232 q = 1) (hb : d249350 q = 1) : d250434 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248232, d249350, d250434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248232, d249350, d250434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248233 q = 1) (hb : d249351 q = 1) : d250435 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248233, d249351, d250435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248233, d249351, d250435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62684 (p : Pattern) (ha : d248239 p = 1) (hb : d249357 p = 1) : d250441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248226 q = 1) (hb : d249344 q = 1) : d250428 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248226, d249344, d250428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62681 q ha hb
    | true =>
      simp only [d248226, d249344, d250428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248227 q = 1) (hb : d249345 q = 1) : d250429 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248227, d249345, d250429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248227, d249345, d250429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248234 q = 1) (hb : d249352 q = 1) : d250436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248234, d249352, d250436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62683 q ha hb
    | true =>
      simp only [d248234, d249352, d250436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248235 q = 1) (hb : d249353 q = 1) : d250437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248235, d249353, d250437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248235, d249353, d250437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248236 q = 1) (hb : d249354 q = 1) : d250438 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248236, d249354, d250438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248236, d249354, d250438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248237 q = 1) (hb : d249355 q = 1) : d250439 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248237, d249355, d250439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248237, d249355, d250439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248238 q = 1) (hb : d249356 q = 1) : d250440 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248238, d249356, d250440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248238, d249356, d250440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248239 q = 1) (hb : d249357 q = 1) : d250441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248239, d249357, d250441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248239, d249357, d250441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62685 (p : Pattern) (ha : d248252 p = 1) (hb : d249365 p = 1) : d250449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248206 q = 1) (hb : d249328 q = 1) : d250413 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62676 q ha hb
    | true =>
      simp only [d248206, d249328, d250413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
  have h2 (q : Pattern) (ha : d248207 q = 1) (hb : d249329 q = 1) : d250414 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248207, d249329, d250414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248208 q = 1) (hb : d249330 q = 1) : d250415 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248208, d249330, d250415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248215 q = 1) (hb : d249333 q = 1) : d250417 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
    | true =>
      simp only [d248215, d249333, d250417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62679 q ha hb
  have h5 (q : Pattern) (ha : d248216 q = 1) (hb : d249334 q = 1) : d250418 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248216, d249334, d250418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248217 q = 1) (hb : d249335 q = 1) : d250419 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248217, d249335, d250419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248218 q = 1) (hb : d249336 q = 1) : d250420 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248218, d249336, d250420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157631 q = 1) : d157631 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d248247 q = 1) (hb : d249360 q = 1) : d250444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248247, d249360, d250444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62678 q ha hb
    | true =>
      simp only [d248247, d249360, d250444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248248 q = 1) (hb : d249361 q = 1) : d250445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248248, d249361, d250445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248248, d249361, d250445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248249 q = 1) (hb : d249362 q = 1) : d250446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248249, d249362, d250446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248249, d249362, d250446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248250 q = 1) (hb : d249363 q = 1) : d250447 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248250, d249363, d250447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248250, d249363, d250447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248251 q = 1) (hb : d249364 q = 1) : d250448 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248251, d249364, d250448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248251, d249364, d250448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248252 q = 1) (hb : d249365 q = 1) : d250449 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248252, d249365, d250449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248252, d249365, d250449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62686 (p : Pattern) (ha : d248258 p = 1) (hb : d249371 p = 1) : d250455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248253 q = 1) (hb : d249366 q = 1) : d250450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248253, d249366, d250450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62685 q ha hb
    | true =>
      simp only [d248253, d249366, d250450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248254 q = 1) (hb : d249367 q = 1) : d250451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248254, d249367, d250451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248254, d249367, d250451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248255 q = 1) (hb : d249368 q = 1) : d250452 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248255, d249368, d250452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248255, d249368, d250452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248256 q = 1) (hb : d249369 q = 1) : d250453 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248256, d249369, d250453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248256, d249369, d250453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248257 q = 1) (hb : d249370 q = 1) : d250454 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248257, d249370, d250454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248257, d249370, d250454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248258 q = 1) (hb : d249371 q = 1) : d250455 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248258, d249371, d250455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248258, d249371, d250455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62687 (p : Pattern) (ha : d248264 p = 1) (hb : d249377 p = 1) : d250461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248240 q = 1) (hb : d249358 q = 1) : d250442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248240, d249358, d250442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62682 q ha hb
    | true =>
      simp only [d248240, d249358, d250442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62684 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248246 q = 1) (hb : d249359 q = 1) : d250443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248246, d249359, d250443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248246, d249359, d250443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d248259 q = 1) (hb : d249372 q = 1) : d250456 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248259, d249372, d250456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62686 q ha hb
    | true =>
      simp only [d248259, d249372, d250456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248260 q = 1) (hb : d249373 q = 1) : d250457 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248260, d249373, d250457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248260, d249373, d250457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248261 q = 1) (hb : d249374 q = 1) : d250458 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248261, d249374, d250458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248261, d249374, d250458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248262 q = 1) (hb : d249375 q = 1) : d250459 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248262, d249375, d250459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248262, d249375, d250459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248263 q = 1) (hb : d249376 q = 1) : d250460 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248263, d249376, d250460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248263, d249376, d250460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248264 q = 1) (hb : d249377 q = 1) : d250461 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248264, d249377, d250461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248264, d249377, d250461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62688 (p : Pattern) (ha : d248244 p = 1) (hb : d249382 p = 1) : d250466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248234 q = 1) (hb : d249352 q = 1) : d250436 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248234, d249352, d250436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62683 q ha hb
    | true =>
      simp only [d248234, d249352, d250436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248235 q = 1) (hb : d249353 q = 1) : d250437 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248235, d249353, d250437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248235, d249353, d250437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248241 q = 1) (hb : d249379 q = 1) : d250463 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248241, d249379, d250463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248241, d249379, d250463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248242 q = 1) (hb : d249380 q = 1) : d250464 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248242, d249380, d250464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248242, d249380, d250464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248243 q = 1) (hb : d249381 q = 1) : d250465 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248243, d249381, d250465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248243, d249381, d250465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248244 q = 1) (hb : d249382 q = 1) : d250466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248244, d249382, d250466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248244, d249382, d250466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62689 (p : Pattern) (ha : d248271 p = 1) (hb : d249388 p = 1) : d250472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248266 q = 1) (hb : d249383 q = 1) : d250467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248266, d249383, d250467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62688 q ha hb
    | true =>
      simp only [d248266, d249383, d250467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248267 q = 1) (hb : d249384 q = 1) : d250468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248267, d249384, d250468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248267, d249384, d250468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248268 q = 1) (hb : d249385 q = 1) : d250469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248268, d249385, d250469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248268, d249385, d250469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248269 q = 1) (hb : d249386 q = 1) : d250470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248269, d249386, d250470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248269, d249386, d250470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248270 q = 1) (hb : d249387 q = 1) : d250471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248270, d249387, d250471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248270, d249387, d250471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248271 q = 1) (hb : d249388 q = 1) : d250472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248271, d249388, d250472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248271, d249388, d250472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62690 (p : Pattern) (ha : d248277 p = 1) (hb : d249394 p = 1) : d250478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248073 q = 1) (hb : d249180 q = 1) : d250304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248073, d249180, d250304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248073, d249180, d250304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62648 q ha hb
  have h2 (q : Pattern) (ha : d248074 q = 1) (hb : d249181 q = 1) : d250305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248074, d249181, d250305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248074, d249181, d250305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248083 q = 1) (hb : d249190 q = 1) : d250314 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248083, d249190, d250314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62648 q ha hb
    | true =>
      simp only [d248083, d249190, d250314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62651 q ha hb
  have h4 (q : Pattern) (ha : d248084 q = 1) (hb : d249191 q = 1) : d250315 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248084, d249191, d250315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248084, d249191, d250315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248085 q = 1) (hb : d249192 q = 1) : d250316 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248085, d249192, d250316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248085, d249192, d250316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248161 q = 1) (hb : d249270 q = 1) : d250384 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248161, d249270, d250384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62663 q ha hb
    | true =>
      simp only [d248161, d249270, d250384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62670 q ha hb
  have h7 (q : Pattern) (ha : d248174 q = 1) (hb : d249283 q = 1) : d250397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248174, d249283, d250397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62671 q ha hb
    | true =>
      simp only [d248174, d249283, d250397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62672 q ha hb
  have h8 (q : Pattern) (ha : d248175 q = 1) (hb : d249284 q = 1) : d250398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248175, d249284, d250398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248175, d249284, d250398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248176 q = 1) (hb : d249285 q = 1) : d250399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248176, d249285, d250399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248176, d249285, d250399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d248177 q = 1) (hb : d249286 q = 1) : d250400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248177, d249286, d250400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248177, d249286, d250400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248181 q = 1) (hb : d249290 q = 1) : d250404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248181, d249290, d250404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248181, d249290, d250404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62673 q ha hb
  have h12 (q : Pattern) (ha : d248183 q = 1) (hb : d249292 q = 1) : d250406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248183, d249292, d250406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248183, d249292, d250406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62674 q ha hb
  have h13 (q : Pattern) (ha : d248184 q = 1) (hb : d249293 q = 1) : d250407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248184, d249293, d250407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248184, d249293, d250407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248185 q = 1) (hb : d249294 q = 1) : d250408 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248185, d249294, d250408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248185, d249294, d250408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d248186 q = 1) (hb : d249295 q = 1) : d250409 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248186, d249295, d250409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d248186, d249295, d250409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d248187 q = 1) (hb : d249296 q = 1) : d250410 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248187, d249296, d250410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248187, d249296, d250410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248265 q = 1) (hb : d249378 q = 1) : d250462 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248265, d249378, d250462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248265, d249378, d250462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62687 q ha hb
  have h18 (q : Pattern) (ha : d248272 q = 1) (hb : d249389 q = 1) : d250473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248272, d249389, d250473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248272, d249389, d250473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62689 q ha hb
  have h19 (q : Pattern) (ha : d248273 q = 1) (hb : d249390 q = 1) : d250474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248273, d249390, d250474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248273, d249390, d250474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d248274 q = 1) (hb : d249391 q = 1) : d250475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248274, d249391, d250475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d248274, d249391, d250475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d248275 q = 1) (hb : d249392 q = 1) : d250476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248275, d249392, d250476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d248275, d249392, d250476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d248276 q = 1) (hb : d249393 q = 1) : d250477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248276, d249393, d250477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d248276, d249393, d250477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d248277 q = 1) (hb : d249394 q = 1) : d250478 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248277, d249394, d250478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248277, d249394, d250478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62691 (p : Pattern) (ha : d248283 p = 1) (hb : d249400 p = 1) : d250484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248278 q = 1) (hb : d249395 q = 1) : d250479 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248278, d249395, d250479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248278, d249395, d250479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62690 q ha hb
  have h2 (q : Pattern) (ha : d248279 q = 1) (hb : d249396 q = 1) : d250480 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248279, d249396, d250480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248279, d249396, d250480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248280 q = 1) (hb : d249397 q = 1) : d250481 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248280, d249397, d250481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248280, d249397, d250481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248281 q = 1) (hb : d249398 q = 1) : d250482 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248281, d249398, d250482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248281, d249398, d250482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248282 q = 1) (hb : d249399 q = 1) : d250483 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248282, d249399, d250483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248282, d249399, d250483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248283 q = 1) (hb : d249400 q = 1) : d250484 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248283, d249400, d250484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248283, d249400, d250484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62692 (p : Pattern) (ha : d27014 p = 1) (hb : d101672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h4 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10349 q = 1) (hb : d101670 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10349, d101670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d10350 q = 1) (hb : d101671 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10350, d101671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10351 q = 1) (hb : d101672 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10351, d101672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d27014 q = 1) (hb : d101672 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62693 (p : Pattern) (ha : d74443 p = 1) (hb : d249405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h4 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5715 q = 1) (hb : d74441 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5715, d74441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d5716 q = 1) (hb : d74442 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5716, d74442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d5717 q = 1) (hb : d74443 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5717, d74443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d74443 q = 1) (hb : d249405 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62694 (p : Pattern) (ha : d248296 p = 1) (hb : d249411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d248288 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
    | true =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d248289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d248290 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d248290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d248290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d248291 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d248291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d248291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d248292 q = 1) (hb : d249406 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
    | true =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248293 q = 1) (hb : d249407 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248294 q = 1) (hb : d249408 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248294, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248294, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248295 q = 1) (hb : d249409 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248295, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248295, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248296 q = 1) (hb : d249410 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248296, d249410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d248296, d249410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d248296 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d248296 q = 1) (hb : d249411 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d249411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62695 (p : Pattern) (ha : d248297 p = 1) (hb : d249418 p = 1) : d250490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248292 q = 1) (hb : d249406 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
    | true =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248293 q = 1) (hb : d249407 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248294 q = 1) (hb : d249408 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248294, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248294, d249408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248295 q = 1) (hb : d249409 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248295, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248295, d249409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d249416 q = 1) : d249416 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d248297 q = 1) (hb : d249417 q = 1) : d250489 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248297, d249417, d250489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248297, d249417, d250489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d248297 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d248297 q = 1) (hb : d249418 q = 1) : d250490 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249418, d250490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d249418, d250490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro62696 (p : Pattern) (ha : d101731 p = 1) (hb : d249412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d101731 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2058 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h3 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h4 (q : Pattern) (ha : d2059 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2076 q = 1) (hb : d53355 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2076, d53355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10409 q = 1) (hb : d101730 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10409, d101730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10410 q = 1) (hb : d101731 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10410, d101731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d101731 q = 1) (hb : d249412 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d249412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro62697 (p : Pattern) (ha : d248305 p = 1) (hb : d249423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248301 q = 1) (hb : d249413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248301, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62696 q ha hb
    | true =>
      simp only [d248301, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248302 q = 1) (hb : d249414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248302, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248302, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248303 q = 1) (hb : d249415 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248303, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248303, d249415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248304 q = 1) (hb : d249416 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248304, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248304, d249416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248305 q = 1) (hb : d249422 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248305, d249422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248305, d249422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d248305 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d248305 q = 1) (hb : d249423 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d249423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62698 (p : Pattern) (ha : d248312 p = 1) (hb : d249430 p = 1) : d250500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248298 q = 1) (hb : d249419 q = 1) : d250491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62694 q ha hb
    | true =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
  have h2 (q : Pattern) (ha : d248299 q = 1) (hb : d249420 q = 1) : d250492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248300 q = 1) (hb : d249421 q = 1) : d250493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248306 q = 1) (hb : d249424 q = 1) : d250494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
    | true =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62697 q ha hb
  have h5 (q : Pattern) (ha : d248307 q = 1) (hb : d249425 q = 1) : d250495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248308 q = 1) (hb : d249426 q = 1) : d250496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248309 q = 1) (hb : d249427 q = 1) : d250497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248310 q = 1) (hb : d249428 q = 1) : d250498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248310, d249428, d250498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248310, d249428, d250498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248311 q = 1) (hb : d249429 q = 1) : d250499 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248311, d249429, d250499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248311, d249429, d250499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248312 q = 1) (hb : d249430 q = 1) : d250500 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248312, d249430, d250500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248312, d249430, d250500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62699 (p : Pattern) (ha : d248316 p = 1) (hb : d249434 p = 1) : d250504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248306 q = 1) (hb : d249424 q = 1) : d250494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
    | true =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62697 q ha hb
  have h2 (q : Pattern) (ha : d248307 q = 1) (hb : d249425 q = 1) : d250495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248308 q = 1) (hb : d249426 q = 1) : d250496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248310 q = 1) (hb : d249428 q = 1) : d250498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248310, d249428, d250498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248310, d249428, d250498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248315 q = 1) (hb : d249433 q = 1) : d250503 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248315, d249433, d250503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248315, d249433, d250503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248316 q = 1) (hb : d249434 q = 1) : d250504 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248316, d249434, d250504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248316, d249434, d250504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62700 (p : Pattern) (ha : d248322 p = 1) (hb : d249440 p = 1) : d250510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248320 q = 1) (hb : d249438 q = 1) : d250508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248321 q = 1) (hb : d249439 q = 1) : d250509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248321, d249439, d250509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248321, d249439, d250509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248322 q = 1) (hb : d249440 q = 1) : d250510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248322, d249440, d250510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248322, d249440, d250510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62701 (p : Pattern) (ha : d248326 p = 1) (hb : d249444 p = 1) : d250514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248324 q = 1) (hb : d249442 q = 1) : d250512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248325 q = 1) (hb : d249443 q = 1) : d250513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248325, d249443, d250513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248325, d249443, d250513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248326 q = 1) (hb : d249444 q = 1) : d250514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248326, d249444, d250514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248326, d249444, d250514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62702 (p : Pattern) (ha : d248332 p = 1) (hb : d249450 p = 1) : d250520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248327 q = 1) (hb : d249445 q = 1) : d250515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
    | true =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
  have h2 (q : Pattern) (ha : d248328 q = 1) (hb : d249446 q = 1) : d250516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248329 q = 1) (hb : d249447 q = 1) : d250517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248330 q = 1) (hb : d249448 q = 1) : d250518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248331 q = 1) (hb : d249449 q = 1) : d250519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248332 q = 1) (hb : d249450 q = 1) : d250520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248332, d249450, d250520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248332, d249450, d250520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62703 (p : Pattern) (ha : d248335 p = 1) (hb : d249453 p = 1) : d250523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248320 q = 1) (hb : d249438 q = 1) : d250508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248321 q = 1) (hb : d249439 q = 1) : d250509 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248321, d249439, d250509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248321, d249439, d250509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248335 q = 1) (hb : d249453 q = 1) : d250523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248335, d249453, d250523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248335, d249453, d250523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62704 (p : Pattern) (ha : d248336 p = 1) (hb : d249454 p = 1) : d250524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248324 q = 1) (hb : d249442 q = 1) : d250512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248325 q = 1) (hb : d249443 q = 1) : d250513 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248325, d249443, d250513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248325, d249443, d250513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248336 q = 1) (hb : d249454 q = 1) : d250524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248336, d249454, d250524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248336, d249454, d250524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62705 (p : Pattern) (ha : d248342 p = 1) (hb : d249460 p = 1) : d250530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248327 q = 1) (hb : d249445 q = 1) : d250515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
    | true =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
  have h2 (q : Pattern) (ha : d248328 q = 1) (hb : d249446 q = 1) : d250516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248329 q = 1) (hb : d249447 q = 1) : d250517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248330 q = 1) (hb : d249448 q = 1) : d250518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248331 q = 1) (hb : d249449 q = 1) : d250519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248337 q = 1) (hb : d249455 q = 1) : d250525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62703 q ha hb
    | true =>
      simp only [d248337, d249455, d250525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62704 q ha hb
  have h7 (q : Pattern) (ha : d248338 q = 1) (hb : d249456 q = 1) : d250526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248338, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248338, d249456, d250526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248339 q = 1) (hb : d249457 q = 1) : d250527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248339, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248339, d249457, d250527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248340 q = 1) (hb : d249458 q = 1) : d250528 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248340, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248340, d249458, d250528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248341 q = 1) (hb : d249459 q = 1) : d250529 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248341, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248341, d249459, d250529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248342 q = 1) (hb : d249460 q = 1) : d250530 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248342, d249460, d250530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248342, d249460, d250530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62706 (p : Pattern) (ha : d248347 p = 1) (hb : d249465 p = 1) : d250535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248320 q = 1) (hb : d249438 q = 1) : d250508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248346 q = 1) (hb : d249464 q = 1) : d250534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248346, d249464, d250534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248346, d249464, d250534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248347 q = 1) (hb : d249465 q = 1) : d250535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248347, d249465, d250535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248347, d249465, d250535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62707 (p : Pattern) (ha : d248349 p = 1) (hb : d249467 p = 1) : d250537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248324 q = 1) (hb : d249442 q = 1) : d250512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248348 q = 1) (hb : d249466 q = 1) : d250536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248348, d249466, d250536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248348, d249466, d250536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248349 q = 1) (hb : d249467 q = 1) : d250537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248349, d249467, d250537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248349, d249467, d250537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62708 (p : Pattern) (ha : d248356 p = 1) (hb : d249474 p = 1) : d250544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248354 q = 1) (hb : d249472 q = 1) : d250542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248354, d249472, d250542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248354, d249472, d250542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248355 q = 1) (hb : d249473 q = 1) : d250543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248355, d249473, d250543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248355, d249473, d250543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248356 q = 1) (hb : d249474 q = 1) : d250544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248356, d249474, d250544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248356, d249474, d250544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62709 (p : Pattern) (ha : d248359 p = 1) (hb : d249477 p = 1) : d250547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248357 q = 1) (hb : d249475 q = 1) : d250545 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248357, d249475, d250545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248357, d249475, d250545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248358 q = 1) (hb : d249476 q = 1) : d250546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248358, d249476, d250546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248358, d249476, d250546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248359 q = 1) (hb : d249477 q = 1) : d250547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248359, d249477, d250547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248359, d249477, d250547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62710 (p : Pattern) (ha : d157794 p = 1) (hb : d248363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d248288 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
    | true =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d248289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d248290 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d248290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d248290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d248291 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d248291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d248291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27105 q = 1) (hb : d248363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27105, d248363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27105, d248363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d248363 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d157794 q = 1) (hb : d248363 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62711 (p : Pattern) (ha : d248369 p = 1) (hb : d249486 p = 1) : d250553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248364 q = 1) (hb : d249481 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248364, d249481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62710 q hb ha
    | true =>
      simp only [d248364, d249481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62694 q ha hb
  have h2 (q : Pattern) (ha : d248365 q = 1) (hb : d249482 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248365, d249482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248365, d249482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248366 q = 1) (hb : d249483 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248366, d249483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248366, d249483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248298 q = 1) (hb : d249419 q = 1) : d250491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62694 q ha hb
    | true =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
  have h5 (q : Pattern) (ha : d248299 q = 1) (hb : d249420 q = 1) : d250492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248300 q = 1) (hb : d249421 q = 1) : d250493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248367 q = 1) (hb : d249484 q = 1) : d250551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248367, d249484, d250551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248367, d249484, d250551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248306 q = 1) (hb : d249424 q = 1) : d250494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
    | true =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62697 q ha hb
  have h9 (q : Pattern) (ha : d248307 q = 1) (hb : d249425 q = 1) : d250495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248308 q = 1) (hb : d249426 q = 1) : d250496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248309 q = 1) (hb : d249427 q = 1) : d250497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248368 q = 1) (hb : d249485 q = 1) : d250552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248368, d249485, d250552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248368, d249485, d250552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248369 q = 1) (hb : d249486 q = 1) : d250553 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248369, d249486, d250553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d248369, d249486, d250553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62712 (p : Pattern) (ha : d248375 p = 1) (hb : d249492 p = 1) : d250559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248370 q = 1) (hb : d249487 q = 1) : d250554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248370, d249487, d250554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62711 q ha hb
    | true =>
      simp only [d248370, d249487, d250554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248371 q = 1) (hb : d249488 q = 1) : d250555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248371, d249488, d250555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248371, d249488, d250555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248372 q = 1) (hb : d249489 q = 1) : d250556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248372, d249489, d250556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248372, d249489, d250556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248373 q = 1) (hb : d249490 q = 1) : d250557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248373, d249490, d250557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248373, d249490, d250557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248374 q = 1) (hb : d249491 q = 1) : d250558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248374, d249491, d250558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248374, d249491, d250558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248375 q = 1) (hb : d249492 q = 1) : d250559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248375, d249492, d250559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248375, d249492, d250559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62713 (p : Pattern) (ha : d248383 p = 1) (hb : d249500 p = 1) : d250567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248298 q = 1) (hb : d249419 q = 1) : d250491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62694 q ha hb
    | true =>
      simp only [d248298, d249419, d250491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
  have h2 (q : Pattern) (ha : d248299 q = 1) (hb : d249420 q = 1) : d250492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248299, d249420, d250492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248300 q = 1) (hb : d249421 q = 1) : d250493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248300, d249421, d250493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248306 q = 1) (hb : d249424 q = 1) : d250494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
    | true =>
      simp only [d248306, d249424, d250494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62697 q ha hb
  have h5 (q : Pattern) (ha : d248307 q = 1) (hb : d249425 q = 1) : d250495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248307, d249425, d250495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248308 q = 1) (hb : d249426 q = 1) : d250496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248308, d249426, d250496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248309 q = 1) (hb : d249427 q = 1) : d250497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248309, d249427, d250497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157731 q = 1) : d157731 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d248378 q = 1) (hb : d249495 q = 1) : d250562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248378, d249495, d250562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62695 q ha hb
    | true =>
      simp only [d248378, d249495, d250562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248379 q = 1) (hb : d249496 q = 1) : d250563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248379, d249496, d250563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248379, d249496, d250563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248380 q = 1) (hb : d249497 q = 1) : d250564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248380, d249497, d250564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248380, d249497, d250564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248381 q = 1) (hb : d249498 q = 1) : d250565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248381, d249498, d250565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248381, d249498, d250565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248382 q = 1) (hb : d249499 q = 1) : d250566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248382, d249499, d250566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248382, d249499, d250566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248383 q = 1) (hb : d249500 q = 1) : d250567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248383, d249500, d250567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248383, d249500, d250567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62714 (p : Pattern) (ha : d248389 p = 1) (hb : d249506 p = 1) : d250573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248384 q = 1) (hb : d249501 q = 1) : d250568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248384, d249501, d250568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62713 q ha hb
    | true =>
      simp only [d248384, d249501, d250568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248385 q = 1) (hb : d249502 q = 1) : d250569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248385, d249502, d250569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248385, d249502, d250569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248386 q = 1) (hb : d249503 q = 1) : d250570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248386, d249503, d250570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248386, d249503, d250570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248387 q = 1) (hb : d249504 q = 1) : d250571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248387, d249504, d250571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248387, d249504, d250571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248388 q = 1) (hb : d249505 q = 1) : d250572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248388, d249505, d250572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248388, d249505, d250572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248389 q = 1) (hb : d249506 q = 1) : d250573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248389, d249506, d250573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248389, d249506, d250573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62715 (p : Pattern) (ha : d248395 p = 1) (hb : d249512 p = 1) : d250579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248350 q = 1) (hb : d249468 q = 1) : d250538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248350, d249468, d250538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62706 q ha hb
    | true =>
      simp only [d248350, d249468, d250538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62707 q ha hb
  have h2 (q : Pattern) (ha : d248351 q = 1) (hb : d249469 q = 1) : d250539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248351, d249469, d250539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248351, d249469, d250539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248352 q = 1) (hb : d249470 q = 1) : d250540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248352, d249470, d250540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248352, d249470, d250540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248353 q = 1) (hb : d249471 q = 1) : d250541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248353, d249471, d250541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248353, d249471, d250541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248360 q = 1) (hb : d249478 q = 1) : d250548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248360, d249478, d250548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62708 q ha hb
    | true =>
      simp only [d248360, d249478, d250548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62709 q ha hb
  have h6 (q : Pattern) (ha : d248361 q = 1) (hb : d249479 q = 1) : d250549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248361, d249479, d250549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248361, d249479, d250549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248362 q = 1) (hb : d249480 q = 1) : d250550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248362, d249480, d250550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248362, d249480, d250550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248376 q = 1) (hb : d249493 q = 1) : d250560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248376, d249493, d250560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62712 q ha hb
    | true =>
      simp only [d248376, d249493, d250560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248377 q = 1) (hb : d249494 q = 1) : d250561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248377, d249494, d250561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248377, d249494, d250561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d248390 q = 1) (hb : d249507 q = 1) : d250574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248390, d249507, d250574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62714 q ha hb
    | true =>
      simp only [d248390, d249507, d250574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d248391 q = 1) (hb : d249508 q = 1) : d250575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248391, d249508, d250575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248391, d249508, d250575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248392 q = 1) (hb : d249509 q = 1) : d250576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248392, d249509, d250576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248392, d249509, d250576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248393 q = 1) (hb : d249510 q = 1) : d250577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248393, d249510, d250577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248393, d249510, d250577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248394 q = 1) (hb : d249511 q = 1) : d250578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248394, d249511, d250578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248394, d249511, d250578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248395 q = 1) (hb : d249512 q = 1) : d250579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248395, d249512, d250579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248395, d249512, d250579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro62716 (p : Pattern) (ha : d248396 p = 1) (hb : d249513 p = 1) : d250580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248320 q = 1) (hb : d249438 q = 1) : d250508 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248320, d249438, d250508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248346 q = 1) (hb : d249464 q = 1) : d250534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248346, d249464, d250534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248346, d249464, d250534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248396 q = 1) (hb : d249513 q = 1) : d250580 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248396, d249513, d250580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248396, d249513, d250580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62717 (p : Pattern) (ha : d248397 p = 1) (hb : d249514 p = 1) : d250581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248324 q = 1) (hb : d249442 q = 1) : d250512 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248324, d249442, d250512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248348 q = 1) (hb : d249466 q = 1) : d250536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248348, d249466, d250536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248348, d249466, d250536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248397 q = 1) (hb : d249514 q = 1) : d250581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248397, d249514, d250581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248397, d249514, d250581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62718 (p : Pattern) (ha : d248402 p = 1) (hb : d249519 p = 1) : d250586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248319 q = 1) (hb : d249437 q = 1) : d250507 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248319, d249437, d250507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248354 q = 1) (hb : d249472 q = 1) : d250542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248354, d249472, d250542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248354, d249472, d250542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248355 q = 1) (hb : d249473 q = 1) : d250543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248355, d249473, d250543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248355, d249473, d250543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248402 q = 1) (hb : d249519 q = 1) : d250586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248402, d249519, d250586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248402, d249519, d250586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62719 (p : Pattern) (ha : d248403 p = 1) (hb : d249520 p = 1) : d250587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248317 q = 1) (hb : d249435 q = 1) : d250505 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62699 q ha hb
    | true =>
      simp only [d248317, d249435, d250505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248318 q = 1) (hb : d249436 q = 1) : d250506 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248318, d249436, d250506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248323 q = 1) (hb : d249441 q = 1) : d250511 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248323, d249441, d250511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248357 q = 1) (hb : d249475 q = 1) : d250545 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248357, d249475, d250545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248357, d249475, d250545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248358 q = 1) (hb : d249476 q = 1) : d250546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248358, d249476, d250546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248358, d249476, d250546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248403 q = 1) (hb : d249520 q = 1) : d250587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248403, d249520, d250587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248403, d249520, d250587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62720 (p : Pattern) (ha : d248407 p = 1) (hb : d249524 p = 1) : d250591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248370 q = 1) (hb : d249487 q = 1) : d250554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248370, d249487, d250554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62711 q ha hb
    | true =>
      simp only [d248370, d249487, d250554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248371 q = 1) (hb : d249488 q = 1) : d250555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248371, d249488, d250555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248371, d249488, d250555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248313 q = 1) (hb : d249431 q = 1) : d250501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62698 q ha hb
    | true =>
      simp only [d248313, d249431, d250501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248314 q = 1) (hb : d249432 q = 1) : d250502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248314, d249432, d250502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248372 q = 1) (hb : d249489 q = 1) : d250556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248372, d249489, d250556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248372, d249489, d250556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248373 q = 1) (hb : d249490 q = 1) : d250557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248373, d249490, d250557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248373, d249490, d250557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248374 q = 1) (hb : d249491 q = 1) : d250558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248374, d249491, d250558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248374, d249491, d250558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248407 q = 1) (hb : d249524 q = 1) : d250591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248407, d249524, d250591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248407, d249524, d250591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62721 (p : Pattern) (ha : d248410 p = 1) (hb : d249527 p = 1) : d250594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248384 q = 1) (hb : d249501 q = 1) : d250568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248384, d249501, d250568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62713 q ha hb
    | true =>
      simp only [d248384, d249501, d250568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248385 q = 1) (hb : d249502 q = 1) : d250569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248385, d249502, d250569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248385, d249502, d250569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248386 q = 1) (hb : d249503 q = 1) : d250570 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248386, d249503, d250570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248386, d249503, d250570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248387 q = 1) (hb : d249504 q = 1) : d250571 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248387, d249504, d250571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248387, d249504, d250571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248388 q = 1) (hb : d249505 q = 1) : d250572 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248388, d249505, d250572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248388, d249505, d250572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248410 q = 1) (hb : d249527 q = 1) : d250594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248410, d249527, d250594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248410, d249527, d250594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62722 (p : Pattern) (ha : d248416 p = 1) (hb : d249533 p = 1) : d250600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248350 q = 1) (hb : d249468 q = 1) : d250538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248350, d249468, d250538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62706 q ha hb
    | true =>
      simp only [d248350, d249468, d250538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62707 q ha hb
  have h2 (q : Pattern) (ha : d248351 q = 1) (hb : d249469 q = 1) : d250539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248351, d249469, d250539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248351, d249469, d250539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248352 q = 1) (hb : d249470 q = 1) : d250540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248352, d249470, d250540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248352, d249470, d250540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248353 q = 1) (hb : d249471 q = 1) : d250541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248353, d249471, d250541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248353, d249471, d250541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248360 q = 1) (hb : d249478 q = 1) : d250548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248360, d249478, d250548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62708 q ha hb
    | true =>
      simp only [d248360, d249478, d250548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62709 q ha hb
  have h6 (q : Pattern) (ha : d248361 q = 1) (hb : d249479 q = 1) : d250549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248361, d249479, d250549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248361, d249479, d250549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248362 q = 1) (hb : d249480 q = 1) : d250550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248362, d249480, d250550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248362, d249480, d250550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248376 q = 1) (hb : d249493 q = 1) : d250560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248376, d249493, d250560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62712 q ha hb
    | true =>
      simp only [d248376, d249493, d250560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248377 q = 1) (hb : d249494 q = 1) : d250561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248377, d249494, d250561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248377, d249494, d250561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d248390 q = 1) (hb : d249507 q = 1) : d250574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248390, d249507, d250574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62714 q ha hb
    | true =>
      simp only [d248390, d249507, d250574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d248391 q = 1) (hb : d249508 q = 1) : d250575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248391, d249508, d250575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248391, d249508, d250575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248392 q = 1) (hb : d249509 q = 1) : d250576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248392, d249509, d250576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248392, d249509, d250576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248393 q = 1) (hb : d249510 q = 1) : d250577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248393, d249510, d250577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248393, d249510, d250577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248394 q = 1) (hb : d249511 q = 1) : d250578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248394, d249511, d250578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248394, d249511, d250578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248398 q = 1) (hb : d249515 q = 1) : d250582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248398, d249515, d250582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62716 q ha hb
    | true =>
      simp only [d248398, d249515, d250582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62717 q ha hb
  have h17 (q : Pattern) (ha : d248399 q = 1) (hb : d249516 q = 1) : d250583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248399, d249516, d250583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248399, d249516, d250583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d248400 q = 1) (hb : d249517 q = 1) : d250584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248400, d249517, d250584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248400, d249517, d250584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d248401 q = 1) (hb : d249518 q = 1) : d250585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248401, d249518, d250585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248401, d249518, d250585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d248404 q = 1) (hb : d249521 q = 1) : d250588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248404, d249521, d250588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62718 q ha hb
    | true =>
      simp only [d248404, d249521, d250588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62719 q ha hb
  have h21 (q : Pattern) (ha : d248405 q = 1) (hb : d249522 q = 1) : d250589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248405, d249522, d250589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248405, d249522, d250589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d248406 q = 1) (hb : d249523 q = 1) : d250590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248406, d249523, d250590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d248406, d249523, d250590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d248408 q = 1) (hb : d249525 q = 1) : d250592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248408, d249525, d250592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62720 q ha hb
    | true =>
      simp only [d248408, d249525, d250592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62703 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d248337 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d248409 q = 1) (hb : d249526 q = 1) : d250593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248409, d249526, d250593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d248409, d249526, d250593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d248411 q = 1) (hb : d249528 q = 1) : d250595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248411, d249528, d250595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62721 q ha hb
    | true =>
      simp only [d248411, d249528, d250595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d248412 q = 1) (hb : d249529 q = 1) : d250596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248412, d249529, d250596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d248412, d249529, d250596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d248413 q = 1) (hb : d249530 q = 1) : d250597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248413, d249530, d250597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d248413, d249530, d250597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d248414 q = 1) (hb : d249531 q = 1) : d250598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248414, d249531, d250598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d248414, d249531, d250598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d248415 q = 1) (hb : d249532 q = 1) : d250599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248415, d249532, d250599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d248415, d249532, d250599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d248416 q = 1) (hb : d249533 q = 1) : d250600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248416, d249533, d250600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248416, d249533, d250600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro62723 (p : Pattern) (ha : d248423 p = 1) (hb : d249540 p = 1) : d250607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248327 q = 1) (hb : d249445 q = 1) : d250515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62700 q ha hb
    | true =>
      simp only [d248327, d249445, d250515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
  have h2 (q : Pattern) (ha : d248328 q = 1) (hb : d249446 q = 1) : d250516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248328, d249446, d250516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248329 q = 1) (hb : d249447 q = 1) : d250517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248329, d249447, d250517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248330 q = 1) (hb : d249448 q = 1) : d250518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248330, d249448, d250518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248331 q = 1) (hb : d249449 q = 1) : d250519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248331, d249449, d250519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248418 q = 1) (hb : d249535 q = 1) : d250602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248418, d249535, d250602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
    | true =>
      simp only [d248418, d249535, d250602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248419 q = 1) (hb : d249536 q = 1) : d250603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248419, d249536, d250603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248419, d249536, d250603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248420 q = 1) (hb : d249537 q = 1) : d250604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248420, d249537, d250604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248420, d249537, d250604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248421 q = 1) (hb : d249538 q = 1) : d250605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248421, d249538, d250605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248421, d249538, d250605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248422 q = 1) (hb : d249539 q = 1) : d250606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248422, d249539, d250606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248422, d249539, d250606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248423 q = 1) (hb : d249540 q = 1) : d250607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248423, d249540, d250607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248423, d249540, d250607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62724 (p : Pattern) (ha : d248429 p = 1) (hb : d249546 p = 1) : d250613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248418 q = 1) (hb : d249535 q = 1) : d250602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248418, d249535, d250602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62701 q ha hb
    | true =>
      simp only [d248418, d249535, d250602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248419 q = 1) (hb : d249536 q = 1) : d250603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248419, d249536, d250603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248419, d249536, d250603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248420 q = 1) (hb : d249537 q = 1) : d250604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248420, d249537, d250604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248420, d249537, d250604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248421 q = 1) (hb : d249538 q = 1) : d250605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248421, d249538, d250605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248421, d249538, d250605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248422 q = 1) (hb : d249539 q = 1) : d250606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248422, d249539, d250606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248422, d249539, d250606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248424 q = 1) (hb : d249541 q = 1) : d250608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248424, d249541, d250608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62704 q ha hb
    | true =>
      simp only [d248424, d249541, d250608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248425 q = 1) (hb : d249542 q = 1) : d250609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248425, d249542, d250609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248425, d249542, d250609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248426 q = 1) (hb : d249543 q = 1) : d250610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248426, d249543, d250610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248426, d249543, d250610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248427 q = 1) (hb : d249544 q = 1) : d250611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248427, d249544, d250611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248427, d249544, d250611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248428 q = 1) (hb : d249545 q = 1) : d250612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248428, d249545, d250612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248428, d249545, d250612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248429 q = 1) (hb : d249546 q = 1) : d250613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248429, d249546, d250613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248429, d249546, d250613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62725 (p : Pattern) (ha : d248436 p = 1) (hb : d249553 p = 1) : d250620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248408 q = 1) (hb : d249525 q = 1) : d250592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248408, d249525, d250592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62720 q ha hb
    | true =>
      simp only [d248408, d249525, d250592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62703 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248409 q = 1) (hb : d249526 q = 1) : d250593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248409, d249526, d250593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248409, d249526, d250593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d248411 q = 1) (hb : d249528 q = 1) : d250595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248411, d249528, d250595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62721 q ha hb
    | true =>
      simp only [d248411, d249528, d250595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248412 q = 1) (hb : d249529 q = 1) : d250596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248412, d249529, d250596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248412, d249529, d250596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248413 q = 1) (hb : d249530 q = 1) : d250597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248413, d249530, d250597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248413, d249530, d250597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248434 q = 1) (hb : d249551 q = 1) : d250618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248434, d249551, d250618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248434, d249551, d250618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248435 q = 1) (hb : d249552 q = 1) : d250619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248435, d249552, d250619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248435, d249552, d250619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248436 q = 1) (hb : d249553 q = 1) : d250620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248436, d249553, d250620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248436, d249553, d250620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62726 (p : Pattern) (ha : d248438 p = 1) (hb : d249555 p = 1) : d250622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248424 q = 1) (hb : d249541 q = 1) : d250608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248424, d249541, d250608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62704 q ha hb
    | true =>
      simp only [d248424, d249541, d250608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248425 q = 1) (hb : d249542 q = 1) : d250609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248425, d249542, d250609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248425, d249542, d250609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248426 q = 1) (hb : d249543 q = 1) : d250610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248426, d249543, d250610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248426, d249543, d250610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248427 q = 1) (hb : d249544 q = 1) : d250611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248427, d249544, d250611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248427, d249544, d250611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248428 q = 1) (hb : d249545 q = 1) : d250612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248428, d249545, d250612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248428, d249545, d250612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248438 q = 1) (hb : d249555 q = 1) : d250622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248438, d249555, d250622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248438, d249555, d250622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62727 (p : Pattern) (ha : d157885 p = 1) (hb : d248448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d248444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d248444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d248444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d248288 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
    | true =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d248445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d248445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d248445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d248289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d248446 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d248446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d248446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d248447 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d248447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d248447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27271 q = 1) (hb : d248448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27271, d248448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27271, d248448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d248448 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d157885 q = 1) (hb : d248448 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62728 (p : Pattern) (ha : d248453 p = 1) (hb : d249566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d248444 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d248444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d248444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d248288 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62692 q ha hb
    | true =>
      simp only [d27015, d248288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d248445 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d248445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d248445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d248289 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d248289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d248446 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d248446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d248446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d248447 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d248447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d248447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d248449 q = 1) (hb : d249561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248449, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248449, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
  have h8 (q : Pattern) (ha : d248292 q = 1) (hb : d249406 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
    | true =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248450 q = 1) (hb : d249562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248450, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248450, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248293 q = 1) (hb : d249407 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d248451 q = 1) (hb : d249563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248451, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248451, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248452 q = 1) (hb : d249564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248452, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248452, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248453 q = 1) (hb : d249565 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248453, d249565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d248453, d249565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d248453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d248453 q = 1) (hb : d249566 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d249566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62729 (p : Pattern) (ha : d248457 p = 1) (hb : d249575 p = 1) : d250629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248449 q = 1) (hb : d249561 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248449, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248449, d249561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
  have h2 (q : Pattern) (ha : d248292 q = 1) (hb : d249406 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62693 q ha hb
    | true =>
      simp only [d248292, d249406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248450 q = 1) (hb : d249562 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248450, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248450, d249562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248293 q = 1) (hb : d249407 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248293, d249407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248451 q = 1) (hb : d249563 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248451, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248451, d249563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248452 q = 1) (hb : d249564 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248452, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248452, d249564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d249573 q = 1) : d249573 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d248457 q = 1) (hb : d249574 q = 1) : d250628 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248457, d249574, d250628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248457, d249574, d250628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d248457 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d248457 q = 1) (hb : d249575 q = 1) : d250629 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249575, d250629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d249575, d250629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro62730 (p : Pattern) (ha : d248466 p = 1) (hb : d249581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248462 q = 1) (hb : d249570 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248462, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248462, d249570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62696 q ha hb
  have h2 (q : Pattern) (ha : d248301 q = 1) (hb : d249413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d248301, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62696 q ha hb
    | true =>
      simp only [d248301, d249413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248463 q = 1) (hb : d249571 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248463, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248463, d249571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248302 q = 1) (hb : d249414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d248302, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248302, d249414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248464 q = 1) (hb : d249572 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d248464, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248464, d249572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248465 q = 1) (hb : d249573 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248465, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248465, d249573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248466 q = 1) (hb : d249580 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d248466, d249580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248466, d249580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d248466 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d248466 q = 1) (hb : d249581 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d249581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d249581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro62731 (p : Pattern) (ha : d248472 p = 1) (hb : d249587 p = 1) : d250639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248454 q = 1) (hb : d249567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248454, d249567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62727 q hb ha
    | true =>
      simp only [d248454, d249567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62728 q ha hb
  have h2 (q : Pattern) (ha : d248455 q = 1) (hb : d249568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248455, d249568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248455, d249568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248456 q = 1) (hb : d249569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248456, d249569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248456, d249569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248458 q = 1) (hb : d249576 q = 1) : d250630 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62728 q ha hb
    | true =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
  have h5 (q : Pattern) (ha : d248459 q = 1) (hb : d249577 q = 1) : d250631 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248460 q = 1) (hb : d249578 q = 1) : d250632 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248461 q = 1) (hb : d249579 q = 1) : d250633 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248461, d249579, d250633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248461, d249579, d250633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248467 q = 1) (hb : d249582 q = 1) : d250634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
    | true =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62730 q ha hb
  have h9 (q : Pattern) (ha : d248468 q = 1) (hb : d249583 q = 1) : d250635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248469 q = 1) (hb : d249584 q = 1) : d250636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248470 q = 1) (hb : d249585 q = 1) : d250637 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248471 q = 1) (hb : d249586 q = 1) : d250638 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248471, d249586, d250638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248471, d249586, d250638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248472 q = 1) (hb : d249587 q = 1) : d250639 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248472, d249587, d250639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d248472, d249587, d250639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62732 (p : Pattern) (ha : d248477 p = 1) (hb : d249592 p = 1) : d250644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248458 q = 1) (hb : d249576 q = 1) : d250630 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62728 q ha hb
    | true =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
  have h2 (q : Pattern) (ha : d248459 q = 1) (hb : d249577 q = 1) : d250631 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248460 q = 1) (hb : d249578 q = 1) : d250632 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248467 q = 1) (hb : d249582 q = 1) : d250634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
    | true =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62730 q ha hb
  have h5 (q : Pattern) (ha : d248468 q = 1) (hb : d249583 q = 1) : d250635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248469 q = 1) (hb : d249584 q = 1) : d250636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248470 q = 1) (hb : d249585 q = 1) : d250637 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248475 q = 1) (hb : d249590 q = 1) : d250642 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248475, d249590, d250642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248475, d249590, d250642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d248476 q = 1) (hb : d249591 q = 1) : d250643 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248476, d249591, d250643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248476, d249591, d250643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248477 q = 1) (hb : d249592 q = 1) : d250644 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248477, d249592, d250644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d248477, d249592, d250644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62733 (p : Pattern) (ha : d248483 p = 1) (hb : d249598 p = 1) : d250650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248473 q = 1) (hb : d249588 q = 1) : d250640 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248473, d249588, d250640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62731 q ha hb
    | true =>
      simp only [d248473, d249588, d250640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248474 q = 1) (hb : d249589 q = 1) : d250641 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248474, d249589, d250641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248474, d249589, d250641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248478 q = 1) (hb : d249593 q = 1) : d250645 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248478, d249593, d250645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62732 q ha hb
    | true =>
      simp only [d248478, d249593, d250645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248479 q = 1) (hb : d249594 q = 1) : d250646 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248479, d249594, d250646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248479, d249594, d250646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248480 q = 1) (hb : d249595 q = 1) : d250647 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248480, d249595, d250647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248480, d249595, d250647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248481 q = 1) (hb : d249596 q = 1) : d250648 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248481, d249596, d250648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248481, d249596, d250648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248482 q = 1) (hb : d249597 q = 1) : d250649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248482, d249597, d250649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248482, d249597, d250649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248483 q = 1) (hb : d249598 q = 1) : d250650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248483, d249598, d250650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248483, d249598, d250650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62734 (p : Pattern) (ha : d248485 p = 1) (hb : d249600 p = 1) : d250652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248467 q = 1) (hb : d249582 q = 1) : d250634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
    | true =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62730 q ha hb
  have h2 (q : Pattern) (ha : d248468 q = 1) (hb : d249583 q = 1) : d250635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248469 q = 1) (hb : d249584 q = 1) : d250636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248475 q = 1) (hb : d249590 q = 1) : d250642 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248475, d249590, d250642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248475, d249590, d250642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248484 q = 1) (hb : d249599 q = 1) : d250651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248484, d249599, d250651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248484, d249599, d250651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248485 q = 1) (hb : d249600 q = 1) : d250652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248485, d249600, d250652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248485, d249600, d250652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62735 (p : Pattern) (ha : d248491 p = 1) (hb : d249606 p = 1) : d250658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248478 q = 1) (hb : d249593 q = 1) : d250645 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248478, d249593, d250645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62732 q ha hb
    | true =>
      simp only [d248478, d249593, d250645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248479 q = 1) (hb : d249594 q = 1) : d250646 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248479, d249594, d250646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248479, d249594, d250646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248486 q = 1) (hb : d249601 q = 1) : d250653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248486, d249601, d250653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62734 q ha hb
    | true =>
      simp only [d248486, d249601, d250653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248487 q = 1) (hb : d249602 q = 1) : d250654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248487, d249602, d250654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248487, d249602, d250654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248488 q = 1) (hb : d249603 q = 1) : d250655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248488, d249603, d250655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248488, d249603, d250655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248489 q = 1) (hb : d249604 q = 1) : d250656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248489, d249604, d250656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248489, d249604, d250656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d248490 q = 1) (hb : d249605 q = 1) : d250657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248490, d249605, d250657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248490, d249605, d250657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d248491 q = 1) (hb : d249606 q = 1) : d250658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248491, d249606, d250658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248491, d249606, d250658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62736 (p : Pattern) (ha : d248504 p = 1) (hb : d249614 p = 1) : d250666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248458 q = 1) (hb : d249576 q = 1) : d250630 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62728 q ha hb
    | true =>
      simp only [d248458, d249576, d250630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
  have h2 (q : Pattern) (ha : d248459 q = 1) (hb : d249577 q = 1) : d250631 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248459, d249577, d250631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248460 q = 1) (hb : d249578 q = 1) : d250632 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248460, d249578, d250632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248467 q = 1) (hb : d249582 q = 1) : d250634 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
    | true =>
      simp only [d248467, d249582, d250634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62730 q ha hb
  have h5 (q : Pattern) (ha : d248468 q = 1) (hb : d249583 q = 1) : d250635 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248468, d249583, d250635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248469 q = 1) (hb : d249584 q = 1) : d250636 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248469, d249584, d250636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248470 q = 1) (hb : d249585 q = 1) : d250637 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248470, d249585, d250637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d157913 q = 1) : d157913 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d248499 q = 1) (hb : d249609 q = 1) : d250661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d248499, d249609, d250661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62729 q ha hb
    | true =>
      simp only [d248499, d249609, d250661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248500 q = 1) (hb : d249610 q = 1) : d250662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d248500, d249610, d250662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248500, d249610, d250662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248501 q = 1) (hb : d249611 q = 1) : d250663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d248501, d249611, d250663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248501, d249611, d250663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d248502 q = 1) (hb : d249612 q = 1) : d250664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d248502, d249612, d250664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248502, d249612, d250664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d248503 q = 1) (hb : d249613 q = 1) : d250665 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d248503, d249613, d250665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d248503, d249613, d250665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248504 q = 1) (hb : d249614 q = 1) : d250666 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d248504, d249614, d250666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248504, d249614, d250666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro62737 (p : Pattern) (ha : d248510 p = 1) (hb : d249620 p = 1) : d250672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248505 q = 1) (hb : d249615 q = 1) : d250667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248505, d249615, d250667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62736 q ha hb
    | true =>
      simp only [d248505, d249615, d250667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248506 q = 1) (hb : d249616 q = 1) : d250668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248506, d249616, d250668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248506, d249616, d250668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248507 q = 1) (hb : d249617 q = 1) : d250669 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248507, d249617, d250669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248507, d249617, d250669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248508 q = 1) (hb : d249618 q = 1) : d250670 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248508, d249618, d250670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248508, d249618, d250670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248509 q = 1) (hb : d249619 q = 1) : d250671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248509, d249619, d250671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248509, d249619, d250671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248510 q = 1) (hb : d249620 q = 1) : d250672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248510, d249620, d250672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248510, d249620, d250672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62738 (p : Pattern) (ha : d248516 p = 1) (hb : d249626 p = 1) : d250678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248492 q = 1) (hb : d249607 q = 1) : d250659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248492, d249607, d250659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62733 q ha hb
    | true =>
      simp only [d248492, d249607, d250659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62735 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d248497 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d248498 q = 1) (hb : d249608 q = 1) : d250660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248498, d249608, d250660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248498, d249608, d250660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d248511 q = 1) (hb : d249621 q = 1) : d250673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248511, d249621, d250673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62737 q ha hb
    | true =>
      simp only [d248511, d249621, d250673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248512 q = 1) (hb : d249622 q = 1) : d250674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248512, d249622, d250674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248512, d249622, d250674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248513 q = 1) (hb : d249623 q = 1) : d250675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248513, d249623, d250675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248513, d249623, d250675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248514 q = 1) (hb : d249624 q = 1) : d250676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248514, d249624, d250676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248514, d249624, d250676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d248515 q = 1) (hb : d249625 q = 1) : d250677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248515, d249625, d250677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248515, d249625, d250677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248516 q = 1) (hb : d249626 q = 1) : d250678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248516, d249626, d250678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248516, d249626, d250678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62739 (p : Pattern) (ha : d248496 p = 1) (hb : d249631 p = 1) : d250683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248486 q = 1) (hb : d249601 q = 1) : d250653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d248486, d249601, d250653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62734 q ha hb
    | true =>
      simp only [d248486, d249601, d250653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248487 q = 1) (hb : d249602 q = 1) : d250654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d248487, d249602, d250654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248487, d249602, d250654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248493 q = 1) (hb : d249628 q = 1) : d250680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d248493, d249628, d250680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248493, d249628, d250680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248494 q = 1) (hb : d249629 q = 1) : d250681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d248494, d249629, d250681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248494, d249629, d250681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248495 q = 1) (hb : d249630 q = 1) : d250682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d248495, d249630, d250682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248495, d249630, d250682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248496 q = 1) (hb : d249631 q = 1) : d250683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d248496, d249631, d250683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248496, d249631, d250683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62740 (p : Pattern) (ha : d248523 p = 1) (hb : d249637 p = 1) : d250689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248518 q = 1) (hb : d249632 q = 1) : d250684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d248518, d249632, d250684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62739 q ha hb
    | true =>
      simp only [d248518, d249632, d250684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248519 q = 1) (hb : d249633 q = 1) : d250685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d248519, d249633, d250685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248519, d249633, d250685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248520 q = 1) (hb : d249634 q = 1) : d250686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d248520, d249634, d250686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248520, d249634, d250686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248521 q = 1) (hb : d249635 q = 1) : d250687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d248521, d249635, d250687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248521, d249635, d250687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248522 q = 1) (hb : d249636 q = 1) : d250688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d248522, d249636, d250688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248522, d249636, d250688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248523 q = 1) (hb : d249637 q = 1) : d250689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d248523, d249637, d250689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248523, d249637, d250689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62741 (p : Pattern) (ha : d248529 p = 1) (hb : d249643 p = 1) : d250695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248333 q = 1) (hb : d249451 q = 1) : d250521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248333, d249451, d250521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248333, d249451, d250521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62702 q ha hb
  have h2 (q : Pattern) (ha : d248334 q = 1) (hb : d249452 q = 1) : d250522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248334, d249452, d250522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248334, d249452, d250522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248343 q = 1) (hb : d249461 q = 1) : d250531 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248343, d249461, d250531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62702 q ha hb
    | true =>
      simp only [d248343, d249461, d250531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62705 q ha hb
  have h4 (q : Pattern) (ha : d248344 q = 1) (hb : d249462 q = 1) : d250532 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248344, d249462, d250532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248344, d249462, d250532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248345 q = 1) (hb : d249463 q = 1) : d250533 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248345, d249463, d250533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248345, d249463, d250533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248417 q = 1) (hb : d249534 q = 1) : d250601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248417, d249534, d250601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62715 q ha hb
    | true =>
      simp only [d248417, d249534, d250601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62722 q ha hb
  have h7 (q : Pattern) (ha : d248430 q = 1) (hb : d249547 q = 1) : d250614 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248430, d249547, d250614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62723 q ha hb
    | true =>
      simp only [d248430, d249547, d250614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62724 q ha hb
  have h8 (q : Pattern) (ha : d248431 q = 1) (hb : d249548 q = 1) : d250615 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248431, d249548, d250615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248431, d249548, d250615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248432 q = 1) (hb : d249549 q = 1) : d250616 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248432, d249549, d250616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d248432, d249549, d250616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d248433 q = 1) (hb : d249550 q = 1) : d250617 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248433, d249550, d250617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248433, d249550, d250617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248437 q = 1) (hb : d249554 q = 1) : d250621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248437, d249554, d250621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248437, d249554, d250621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62725 q ha hb
  have h12 (q : Pattern) (ha : d248439 q = 1) (hb : d249556 q = 1) : d250623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248439, d249556, d250623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248439, d249556, d250623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62726 q ha hb
  have h13 (q : Pattern) (ha : d248440 q = 1) (hb : d249557 q = 1) : d250624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248440, d249557, d250624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d248440, d249557, d250624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248441 q = 1) (hb : d249558 q = 1) : d250625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248441, d249558, d250625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d248441, d249558, d250625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d248442 q = 1) (hb : d249559 q = 1) : d250626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248442, d249559, d250626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d248442, d249559, d250626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d248443 q = 1) (hb : d249560 q = 1) : d250627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248443, d249560, d250627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248443, d249560, d250627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d248517 q = 1) (hb : d249627 q = 1) : d250679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248517, d249627, d250679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248517, d249627, d250679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62738 q ha hb
  have h18 (q : Pattern) (ha : d248524 q = 1) (hb : d249638 q = 1) : d250690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d248524, d249638, d250690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248524, d249638, d250690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62740 q ha hb
  have h19 (q : Pattern) (ha : d248525 q = 1) (hb : d249639 q = 1) : d250691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d248525, d249639, d250691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d248525, d249639, d250691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d248526 q = 1) (hb : d249640 q = 1) : d250692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d248526, d249640, d250692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d248526, d249640, d250692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d248527 q = 1) (hb : d249641 q = 1) : d250693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d248527, d249641, d250693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d248527, d249641, d250693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d248528 q = 1) (hb : d249642 q = 1) : d250694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d248528, d249642, d250694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d248528, d249642, d250694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d248529 q = 1) (hb : d249643 q = 1) : d250695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d248529, d249643, d250695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d248529, d249643, d250695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62742 (p : Pattern) (ha : d248535 p = 1) (hb : d249649 p = 1) : d250701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248530 q = 1) (hb : d249644 q = 1) : d250696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d248530, d249644, d250696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248530, d249644, d250696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62741 q ha hb
  have h2 (q : Pattern) (ha : d248531 q = 1) (hb : d249645 q = 1) : d250697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d248531, d249645, d250697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248531, d249645, d250697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d248532 q = 1) (hb : d249646 q = 1) : d250698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d248532, d249646, d250698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248532, d249646, d250698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248533 q = 1) (hb : d249647 q = 1) : d250699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d248533, d249647, d250699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248533, d249647, d250699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d248534 q = 1) (hb : d249648 q = 1) : d250700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d248534, d249648, d250700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248534, d249648, d250700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248535 q = 1) (hb : d249649 q = 1) : d250701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d248535, d249649, d250701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d248535, d249649, d250701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62743 (p : Pattern) (ha : d248541 p = 1) (hb : d249655 p = 1) : d250707 p = 1 := by
  have h0 (q : Pattern) (ha : d247606 q = 1) (hb : d248673 q = 1) : d249896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d247606, d248673, d249896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62501 q hb ha
    | true =>
      simp only [d247606, d248673, d249896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62528 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d247767 q = 1) (hb : d248853 q = 1) : d250048 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d247767, d248853, d250048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d247767, d248853, d250048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62578 q ha hb
  have h3 (q : Pattern) (ha : d247768 q = 1) (hb : d248854 q = 1) : d250049 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d247768, d248854, d250049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d247768, d248854, d250049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d248025 q = 1) (hb : d249121 q = 1) : d250269 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248025, d249121, d250269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248025, d249121, d250269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62635 q ha hb
  have h5 (q : Pattern) (ha : d248026 q = 1) (hb : d249122 q = 1) : d250270 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248026, d249122, d250270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248026, d249122, d250270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d248027 q = 1) (hb : d249123 q = 1) : d250271 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248027, d249123, d250271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248027, d249123, d250271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d248284 q = 1) (hb : d249401 q = 1) : d250485 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248284, d249401, d250485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248284, d249401, d250485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62691 q ha hb
  have h8 (q : Pattern) (ha : d248285 q = 1) (hb : d249402 q = 1) : d250486 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248285, d249402, d250486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248285, d249402, d250486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d248286 q = 1) (hb : d249403 q = 1) : d250487 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248286, d249403, d250487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248286, d249403, d250487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d248287 q = 1) (hb : d249404 q = 1) : d250488 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d248287, d249404, d250488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d248287, d249404, d250488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d248536 q = 1) (hb : d249650 q = 1) : d250702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d248536, d249650, d250702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248536, d249650, d250702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62742 q ha hb
  have h12 (q : Pattern) (ha : d248537 q = 1) (hb : d249651 q = 1) : d250703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d248537, d249651, d250703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248537, d249651, d250703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d248538 q = 1) (hb : d249652 q = 1) : d250704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d248538, d249652, d250704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248538, d249652, d250704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d248539 q = 1) (hb : d249653 q = 1) : d250705 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d248539, d249653, d250705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d248539, d249653, d250705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d248540 q = 1) (hb : d249654 q = 1) : d250706 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d248540, d249654, d250706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d248540, d249654, d250706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d248541 q = 1) (hb : d249655 q = 1) : d250707 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d248541, d249655, d250707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d248541, d249655, d250707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62744 (p : Pattern) (ha : d248547 p = 1) (hb : d249661 p = 1) : d250713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248542 q = 1) (hb : d249656 q = 1) : d250708 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d248542, d249656, d250708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62743 q ha hb
    | true =>
      simp only [d248542, d249656, d250708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248543 q = 1) (hb : d249657 q = 1) : d250709 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d248543, d249657, d250709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248543, d249657, d250709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248544 q = 1) (hb : d249658 q = 1) : d250710 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d248544, d249658, d250710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248544, d249658, d250710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248545 q = 1) (hb : d249659 q = 1) : d250711 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d248545, d249659, d250711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248545, d249659, d250711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248546 q = 1) (hb : d249660 q = 1) : d250712 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d248546, d249660, d250712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248546, d249660, d250712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248547 q = 1) (hb : d249661 q = 1) : d250713 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d248547, d249661, d250713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248547, d249661, d250713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62745 (p : Pattern) (ha : d248553 p = 1) (hb : d249667 p = 1) : d250719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248548 q = 1) (hb : d249662 q = 1) : d250714 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d248548, d249662, d250714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62744 q ha hb
    | true =>
      simp only [d248548, d249662, d250714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248549 q = 1) (hb : d249663 q = 1) : d250715 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d248549, d249663, d250715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248549, d249663, d250715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248550 q = 1) (hb : d249664 q = 1) : d250716 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d248550, d249664, d250716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248550, d249664, d250716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248551 q = 1) (hb : d249665 q = 1) : d250717 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d248551, d249665, d250717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248551, d249665, d250717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248552 q = 1) (hb : d249666 q = 1) : d250718 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d248552, d249666, d250718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248552, d249666, d250718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248553 q = 1) (hb : d249667 q = 1) : d250719 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d248553, d249667, d250719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248553, d249667, d250719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62746 (p : Pattern) (ha : d248559 p = 1) (hb : d249673 p = 1) : d250725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248554 q = 1) (hb : d249668 q = 1) : d250720 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d248554, d249668, d250720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62745 q ha hb
    | true =>
      simp only [d248554, d249668, d250720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248555 q = 1) (hb : d249669 q = 1) : d250721 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d248555, d249669, d250721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248555, d249669, d250721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248556 q = 1) (hb : d249670 q = 1) : d250722 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d248556, d249670, d250722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248556, d249670, d250722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248557 q = 1) (hb : d249671 q = 1) : d250723 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d248557, d249671, d250723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248557, d249671, d250723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248558 q = 1) (hb : d249672 q = 1) : d250724 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d248558, d249672, d250724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248558, d249672, d250724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248559 q = 1) (hb : d249673 q = 1) : d250725 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d248559, d249673, d250725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248559, d249673, d250725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62747 (p : Pattern) (ha : d248565 p = 1) (hb : d249679 p = 1) : d250731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248560 q = 1) (hb : d249674 q = 1) : d250726 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d248560, d249674, d250726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62746 q ha hb
    | true =>
      simp only [d248560, d249674, d250726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248561 q = 1) (hb : d249675 q = 1) : d250727 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d248561, d249675, d250727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248561, d249675, d250727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248562 q = 1) (hb : d249676 q = 1) : d250728 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d248562, d249676, d250728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248562, d249676, d250728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248563 q = 1) (hb : d249677 q = 1) : d250729 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d248563, d249677, d250729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248563, d249677, d250729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248564 q = 1) (hb : d249678 q = 1) : d250730 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d248564, d249678, d250730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248564, d249678, d250730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248565 q = 1) (hb : d249679 q = 1) : d250731 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d248565, d249679, d250731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248565, d249679, d250731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62748 (p : Pattern) (ha : d248571 p = 1) (hb : d249685 p = 1) : d250737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248566 q = 1) (hb : d249680 q = 1) : d250732 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d248566, d249680, d250732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62747 q ha hb
    | true =>
      simp only [d248566, d249680, d250732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248567 q = 1) (hb : d249681 q = 1) : d250733 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d248567, d249681, d250733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248567, d249681, d250733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248568 q = 1) (hb : d249682 q = 1) : d250734 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d248568, d249682, d250734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248568, d249682, d250734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248569 q = 1) (hb : d249683 q = 1) : d250735 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d248569, d249683, d250735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248569, d249683, d250735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248570 q = 1) (hb : d249684 q = 1) : d250736 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d248570, d249684, d250736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248570, d249684, d250736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248571 q = 1) (hb : d249685 q = 1) : d250737 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d248571, d249685, d250737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248571, d249685, d250737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62749 (p : Pattern) (ha : d248577 p = 1) (hb : d249691 p = 1) : d250743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d248572 q = 1) (hb : d249686 q = 1) : d250738 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d248572, d249686, d250738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62748 q ha hb
    | true =>
      simp only [d248572, d249686, d250738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d248573 q = 1) (hb : d249687 q = 1) : d250739 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d248573, d249687, d250739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d248573, d249687, d250739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d248574 q = 1) (hb : d249688 q = 1) : d250740 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d248574, d249688, d250740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d248574, d249688, d250740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d248575 q = 1) (hb : d249689 q = 1) : d250741 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d248575, d249689, d250741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d248575, d249689, d250741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d248576 q = 1) (hb : d249690 q = 1) : d250742 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d248576, d249690, d250742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d248576, d249690, d250742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d248577 q = 1) (hb : d249691 q = 1) : d250743 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d248577, d249691, d250743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d248577, d249691, d250743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
