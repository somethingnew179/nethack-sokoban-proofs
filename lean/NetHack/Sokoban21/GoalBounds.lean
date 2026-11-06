/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalSemantic31
import NetHack.Sokoban21.GoalComparisons11
set_option maxRecDepth 10000
namespace NetHack.Sokoban21
open Diagram NetHack.Sokoban.LowerBounds
theorem goal0_semantic (pattern : Twelve) : d3274 pattern = (if decide (0 + (Projection.occupied pattern).length ≤ 3) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
    · exact goal0_shape0 g h i j k l
    · exact goal0_shape1 g h i j k l
    · exact goal0_shape2 g h i j k l
    · exact goal0_shape3 g h i j k l
    · exact goal0_shape4 g h i j k l
    · exact goal0_shape5 g h i j k l
    · exact goal0_shape6 g h i j k l
    · exact goal0_shape7 g h i j k l
    · exact goal0_shape8 g h i j k l
    · exact goal0_shape9 g h i j k l
    · exact goal0_shape10 g h i j k l
    · exact goal0_shape11 g h i j k l
    · exact goal0_shape12 g h i j k l
    · exact goal0_shape13 g h i j k l
    · exact goal0_shape14 g h i j k l
    · exact goal0_shape15 g h i j k l
    · exact goal0_shape16 g h i j k l
    · exact goal0_shape17 g h i j k l
    · exact goal0_shape18 g h i j k l
    · exact goal0_shape19 g h i j k l
    · exact goal0_shape20 g h i j k l
    · exact goal0_shape21 g h i j k l
    · exact goal0_shape22 g h i j k l
    · exact goal0_shape23 g h i j k l
    · exact goal0_shape24 g h i j k l
    · exact goal0_shape25 g h i j k l
    · exact goal0_shape26 g h i j k l
    · exact goal0_shape27 g h i j k l
    · exact goal0_shape28 g h i j k l
    · exact goal0_shape29 g h i j k l
    · exact goal0_shape30 g h i j k l
    · exact goal0_shape31 g h i j k l
    · exact goal0_shape32 g h i j k l
    · exact goal0_shape33 g h i j k l
    · exact goal0_shape34 g h i j k l
    · exact goal0_shape35 g h i j k l
    · exact goal0_shape36 g h i j k l
    · exact goal0_shape37 g h i j k l
    · exact goal0_shape38 g h i j k l
    · exact goal0_shape39 g h i j k l
    · exact goal0_shape40 g h i j k l
    · exact goal0_shape41 g h i j k l
    · exact goal0_shape42 g h i j k l
    · exact goal0_shape43 g h i j k l
    · exact goal0_shape44 g h i j k l
    · exact goal0_shape45 g h i j k l
    · exact goal0_shape46 g h i j k l
    · exact goal0_shape47 g h i j k l
    · exact goal0_shape48 g h i j k l
    · exact goal0_shape49 g h i j k l
    · exact goal0_shape50 g h i j k l
    · exact goal0_shape51 g h i j k l
    · exact goal0_shape52 g h i j k l
    · exact goal0_shape53 g h i j k l
    · exact goal0_shape54 g h i j k l
    · exact goal0_shape55 g h i j k l
    · exact goal0_shape56 g h i j k l
    · exact goal0_shape57 g h i j k l
    · exact goal0_shape58 g h i j k l
    · exact goal0_shape59 g h i j k l
    · exact goal0_shape60 g h i j k l
    · exact goal0_shape61 g h i j k l
    · exact goal0_shape62 g h i j k l
    · exact goal0_shape63 g h i j k l
theorem goal1_semantic (pattern : Twelve) : d3277 pattern = (if decide (1 + (Projection.occupied pattern).length ≤ 3) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
    · exact goal1_shape0 g h i j k l
    · exact goal1_shape1 g h i j k l
    · exact goal1_shape2 g h i j k l
    · exact goal1_shape3 g h i j k l
    · exact goal1_shape4 g h i j k l
    · exact goal1_shape5 g h i j k l
    · exact goal1_shape6 g h i j k l
    · exact goal1_shape7 g h i j k l
    · exact goal1_shape8 g h i j k l
    · exact goal1_shape9 g h i j k l
    · exact goal1_shape10 g h i j k l
    · exact goal1_shape11 g h i j k l
    · exact goal1_shape12 g h i j k l
    · exact goal1_shape13 g h i j k l
    · exact goal1_shape14 g h i j k l
    · exact goal1_shape15 g h i j k l
    · exact goal1_shape16 g h i j k l
    · exact goal1_shape17 g h i j k l
    · exact goal1_shape18 g h i j k l
    · exact goal1_shape19 g h i j k l
    · exact goal1_shape20 g h i j k l
    · exact goal1_shape21 g h i j k l
    · exact goal1_shape22 g h i j k l
    · exact goal1_shape23 g h i j k l
    · exact goal1_shape24 g h i j k l
    · exact goal1_shape25 g h i j k l
    · exact goal1_shape26 g h i j k l
    · exact goal1_shape27 g h i j k l
    · exact goal1_shape28 g h i j k l
    · exact goal1_shape29 g h i j k l
    · exact goal1_shape30 g h i j k l
    · exact goal1_shape31 g h i j k l
    · exact goal1_shape32 g h i j k l
    · exact goal1_shape33 g h i j k l
    · exact goal1_shape34 g h i j k l
    · exact goal1_shape35 g h i j k l
    · exact goal1_shape36 g h i j k l
    · exact goal1_shape37 g h i j k l
    · exact goal1_shape38 g h i j k l
    · exact goal1_shape39 g h i j k l
    · exact goal1_shape40 g h i j k l
    · exact goal1_shape41 g h i j k l
    · exact goal1_shape42 g h i j k l
    · exact goal1_shape43 g h i j k l
    · exact goal1_shape44 g h i j k l
    · exact goal1_shape45 g h i j k l
    · exact goal1_shape46 g h i j k l
    · exact goal1_shape47 g h i j k l
    · exact goal1_shape48 g h i j k l
    · exact goal1_shape49 g h i j k l
    · exact goal1_shape50 g h i j k l
    · exact goal1_shape51 g h i j k l
    · exact goal1_shape52 g h i j k l
    · exact goal1_shape53 g h i j k l
    · exact goal1_shape54 g h i j k l
    · exact goal1_shape55 g h i j k l
    · exact goal1_shape56 g h i j k l
    · exact goal1_shape57 g h i j k l
    · exact goal1_shape58 g h i j k l
    · exact goal1_shape59 g h i j k l
    · exact goal1_shape60 g h i j k l
    · exact goal1_shape61 g h i j k l
    · exact goal1_shape62 g h i j k l
    · exact goal1_shape63 g h i j k l
theorem goal2_semantic (pattern : Twelve) : d3279 pattern = (if decide (2 + (Projection.occupied pattern).length ≤ 3) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
    · exact goal2_shape0 g h i j k l
    · exact goal2_shape1 g h i j k l
    · exact goal2_shape2 g h i j k l
    · exact goal2_shape3 g h i j k l
    · exact goal2_shape4 g h i j k l
    · exact goal2_shape5 g h i j k l
    · exact goal2_shape6 g h i j k l
    · exact goal2_shape7 g h i j k l
    · exact goal2_shape8 g h i j k l
    · exact goal2_shape9 g h i j k l
    · exact goal2_shape10 g h i j k l
    · exact goal2_shape11 g h i j k l
    · exact goal2_shape12 g h i j k l
    · exact goal2_shape13 g h i j k l
    · exact goal2_shape14 g h i j k l
    · exact goal2_shape15 g h i j k l
    · exact goal2_shape16 g h i j k l
    · exact goal2_shape17 g h i j k l
    · exact goal2_shape18 g h i j k l
    · exact goal2_shape19 g h i j k l
    · exact goal2_shape20 g h i j k l
    · exact goal2_shape21 g h i j k l
    · exact goal2_shape22 g h i j k l
    · exact goal2_shape23 g h i j k l
    · exact goal2_shape24 g h i j k l
    · exact goal2_shape25 g h i j k l
    · exact goal2_shape26 g h i j k l
    · exact goal2_shape27 g h i j k l
    · exact goal2_shape28 g h i j k l
    · exact goal2_shape29 g h i j k l
    · exact goal2_shape30 g h i j k l
    · exact goal2_shape31 g h i j k l
    · exact goal2_shape32 g h i j k l
    · exact goal2_shape33 g h i j k l
    · exact goal2_shape34 g h i j k l
    · exact goal2_shape35 g h i j k l
    · exact goal2_shape36 g h i j k l
    · exact goal2_shape37 g h i j k l
    · exact goal2_shape38 g h i j k l
    · exact goal2_shape39 g h i j k l
    · exact goal2_shape40 g h i j k l
    · exact goal2_shape41 g h i j k l
    · exact goal2_shape42 g h i j k l
    · exact goal2_shape43 g h i j k l
    · exact goal2_shape44 g h i j k l
    · exact goal2_shape45 g h i j k l
    · exact goal2_shape46 g h i j k l
    · exact goal2_shape47 g h i j k l
    · exact goal2_shape48 g h i j k l
    · exact goal2_shape49 g h i j k l
    · exact goal2_shape50 g h i j k l
    · exact goal2_shape51 g h i j k l
    · exact goal2_shape52 g h i j k l
    · exact goal2_shape53 g h i j k l
    · exact goal2_shape54 g h i j k l
    · exact goal2_shape55 g h i j k l
    · exact goal2_shape56 g h i j k l
    · exact goal2_shape57 g h i j k l
    · exact goal2_shape58 g h i j k l
    · exact goal2_shape59 g h i j k l
    · exact goal2_shape60 g h i j k l
    · exact goal2_shape61 g h i j k l
    · exact goal2_shape62 g h i j k l
    · exact goal2_shape63 g h i j k l
theorem goal3_semantic (pattern : Twelve) : d3280 pattern = (if decide (3 + (Projection.occupied pattern).length ≤ 3) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
    · exact goal3_shape0 g h i j k l
    · exact goal3_shape1 g h i j k l
    · exact goal3_shape2 g h i j k l
    · exact goal3_shape3 g h i j k l
    · exact goal3_shape4 g h i j k l
    · exact goal3_shape5 g h i j k l
    · exact goal3_shape6 g h i j k l
    · exact goal3_shape7 g h i j k l
    · exact goal3_shape8 g h i j k l
    · exact goal3_shape9 g h i j k l
    · exact goal3_shape10 g h i j k l
    · exact goal3_shape11 g h i j k l
    · exact goal3_shape12 g h i j k l
    · exact goal3_shape13 g h i j k l
    · exact goal3_shape14 g h i j k l
    · exact goal3_shape15 g h i j k l
    · exact goal3_shape16 g h i j k l
    · exact goal3_shape17 g h i j k l
    · exact goal3_shape18 g h i j k l
    · exact goal3_shape19 g h i j k l
    · exact goal3_shape20 g h i j k l
    · exact goal3_shape21 g h i j k l
    · exact goal3_shape22 g h i j k l
    · exact goal3_shape23 g h i j k l
    · exact goal3_shape24 g h i j k l
    · exact goal3_shape25 g h i j k l
    · exact goal3_shape26 g h i j k l
    · exact goal3_shape27 g h i j k l
    · exact goal3_shape28 g h i j k l
    · exact goal3_shape29 g h i j k l
    · exact goal3_shape30 g h i j k l
    · exact goal3_shape31 g h i j k l
    · exact goal3_shape32 g h i j k l
    · exact goal3_shape33 g h i j k l
    · exact goal3_shape34 g h i j k l
    · exact goal3_shape35 g h i j k l
    · exact goal3_shape36 g h i j k l
    · exact goal3_shape37 g h i j k l
    · exact goal3_shape38 g h i j k l
    · exact goal3_shape39 g h i j k l
    · exact goal3_shape40 g h i j k l
    · exact goal3_shape41 g h i j k l
    · exact goal3_shape42 g h i j k l
    · exact goal3_shape43 g h i j k l
    · exact goal3_shape44 g h i j k l
    · exact goal3_shape45 g h i j k l
    · exact goal3_shape46 g h i j k l
    · exact goal3_shape47 g h i j k l
    · exact goal3_shape48 g h i j k l
    · exact goal3_shape49 g h i j k l
    · exact goal3_shape50 g h i j k l
    · exact goal3_shape51 g h i j k l
    · exact goal3_shape52 g h i j k l
    · exact goal3_shape53 g h i j k l
    · exact goal3_shape54 g h i j k l
    · exact goal3_shape55 g h i j k l
    · exact goal3_shape56 g h i j k l
    · exact goal3_shape57 g h i j k l
    · exact goal3_shape58 g h i j k l
    · exact goal3_shape59 g h i j k l
    · exact goal3_shape60 g h i j k l
    · exact goal3_shape61 g h i j k l
    · exact goal3_shape62 g h i j k l
    · exact goal3_shape63 g h i j k l
theorem cap_semantic (pattern : Twelve) : d3292 pattern = min 6 (patternDebt pattern) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f
    · exact cap_shape0 g h i j k l
    · exact cap_shape1 g h i j k l
    · exact cap_shape2 g h i j k l
    · exact cap_shape3 g h i j k l
    · exact cap_shape4 g h i j k l
    · exact cap_shape5 g h i j k l
    · exact cap_shape6 g h i j k l
    · exact cap_shape7 g h i j k l
    · exact cap_shape8 g h i j k l
    · exact cap_shape9 g h i j k l
    · exact cap_shape10 g h i j k l
    · exact cap_shape11 g h i j k l
    · exact cap_shape12 g h i j k l
    · exact cap_shape13 g h i j k l
    · exact cap_shape14 g h i j k l
    · exact cap_shape15 g h i j k l
    · exact cap_shape16 g h i j k l
    · exact cap_shape17 g h i j k l
    · exact cap_shape18 g h i j k l
    · exact cap_shape19 g h i j k l
    · exact cap_shape20 g h i j k l
    · exact cap_shape21 g h i j k l
    · exact cap_shape22 g h i j k l
    · exact cap_shape23 g h i j k l
    · exact cap_shape24 g h i j k l
    · exact cap_shape25 g h i j k l
    · exact cap_shape26 g h i j k l
    · exact cap_shape27 g h i j k l
    · exact cap_shape28 g h i j k l
    · exact cap_shape29 g h i j k l
    · exact cap_shape30 g h i j k l
    · exact cap_shape31 g h i j k l
    · exact cap_shape32 g h i j k l
    · exact cap_shape33 g h i j k l
    · exact cap_shape34 g h i j k l
    · exact cap_shape35 g h i j k l
    · exact cap_shape36 g h i j k l
    · exact cap_shape37 g h i j k l
    · exact cap_shape38 g h i j k l
    · exact cap_shape39 g h i j k l
    · exact cap_shape40 g h i j k l
    · exact cap_shape41 g h i j k l
    · exact cap_shape42 g h i j k l
    · exact cap_shape43 g h i j k l
    · exact cap_shape44 g h i j k l
    · exact cap_shape45 g h i j k l
    · exact cap_shape46 g h i j k l
    · exact cap_shape47 g h i j k l
    · exact cap_shape48 g h i j k l
    · exact cap_shape49 g h i j k l
    · exact cap_shape50 g h i j k l
    · exact cap_shape51 g h i j k l
    · exact cap_shape52 g h i j k l
    · exact cap_shape53 g h i j k l
    · exact cap_shape54 g h i j k l
    · exact cap_shape55 g h i j k l
    · exact cap_shape56 g h i j k l
    · exact cap_shape57 g h i j k l
    · exact cap_shape58 g h i j k l
    · exact cap_shape59 g h i j k l
    · exact cap_shape60 g h i j k l
    · exact cap_shape61 g h i j k l
    · exact cap_shape62 g h i j k l
    · exact cap_shape63 g h i j k l
private theorem if_le {P : Prop} [Decidable P] {a b z : Int}
    (left : a ≤ z) (right : b ≤ z) : (if P then a else b) ≤ z := by
  split <;> assumption
theorem root_goal0 (pattern : Twelve) (guard : d3274 pattern = 1) (player : Nat) :
    Diagram.root 0 player pattern ≤ d3292 pattern := by
  unfold Diagram.root
  simp only [(show (0 : Nat) = 0 from by decide), (show ¬(0 : Nat) = 1 from by decide), (show ¬(0 : Nat) = 2 from by decide), ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC284 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC304 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC311 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC351 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC418 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC452 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC587 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC727 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC734 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC737 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC149 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC219 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC738 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC143 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC729 pattern guard) (range3292 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem root_goal1 (pattern : Twelve) (guard : d3277 pattern = 1) (player : Nat) :
    Diagram.root 1 player pattern ≤ d3292 pattern := by
  unfold Diagram.root
  simp only [(show ¬(1 : Nat) = 0 from by decide), (show (1 : Nat) = 1 from by decide), (show ¬(1 : Nat) = 2 from by decide), ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC843 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC879 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC899 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC906 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC932 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC979 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1007 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1072 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1125 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1132 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1135 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC811 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC834 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1136 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC805 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1127 pattern guard) (range3292 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem root_goal2 (pattern : Twelve) (guard : d3279 pattern = 1) (player : Nat) :
    Diagram.root 2 player pattern ≤ d3292 pattern := by
  unfold Diagram.root
  simp only [(show ¬(2 : Nat) = 0 from by decide), (show ¬(2 : Nat) = 1 from by decide), (show (2 : Nat) = 2 from by decide), ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1207 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1239 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1258 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1265 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1282 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1313 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1332 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1368 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1404 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1411 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1414 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1181 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1198 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1415 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1406 pattern guard) (range3292 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem root_goal3 (pattern : Twelve) (guard : d3280 pattern = 1) (player : Nat) :
    Diagram.root 3 player pattern ≤ d3292 pattern := by
  unfold Diagram.root
  simp only [(show ¬(3 : Nat) = 0 from by decide), (show ¬(3 : Nat) = 1 from by decide), (show ¬(3 : Nat) = 2 from by decide), ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1445 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1459 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1470 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1475 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1483 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1498 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1510 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1525 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1540 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1544 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1547 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1429 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1438 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1548 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1428 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC1541 pattern guard) (range3292 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end NetHack.Sokoban21
