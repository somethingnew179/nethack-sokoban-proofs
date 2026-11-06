import NetHack.Soko11Sparse319.Base
namespace NetHack.Soko11Sparse319
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (afterBoxes nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem mask_bound (p : Pattern) : maskOf p < 16 := by
  cases a : p 185 <;> cases b : p 186 <;> cases c : p 211 <;> cases d : p 212 <;> simp [maskOf,a,b,c,d]
theorem known_agrees (p : Pattern) (cell : Cell) (member : cell ∈ support) : known (maskOf p) cell = p cell := by
  simp only [support,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases a : p 185 <;> cases b : p 186 <;> cases c : p 211 <;> cases d : p 212 <;> simp [maskOf,known,a,b,c,d] <;> decide +kernel
theorem known_subset (p : Pattern) (cell : Cell) (found : known (maskOf p) cell = true) : p cell = true := by
  by_cases a : cell = 185
  · subst cell; exact (known_agrees p 185 (by simp [support])).symm.trans found
  by_cases b : cell = 186
  · subst cell; exact (known_agrees p 186 (by simp [support])).symm.trans found
  by_cases c : cell = 211
  · subst cell; exact (known_agrees p 211 (by simp [support])).symm.trans found
  by_cases d : cell = 212
  · subst cell; exact (known_agrees p 212 (by simp [support])).symm.trans found
  simp only [known,if_neg a,if_neg b,if_neg c,if_neg d] at found
  cases found
theorem bonus_congr (phase hero : Nat) (p q : Pattern) (same : ∀ cell ∈ support, p cell = q cell) : bonus phase hero p = bonus phase hero q := by
  have a := same 185 (by simp [support])
  have b := same 186 (by simp [support])
  have c := same 211 (by simp [support])
  have d := same 212 (by simp [support])
  simp only [bonus,maskOf,a,b,c,d]
theorem after_agrees (p q : Pattern) (outcome : Outcome) (cell : Cell) (same : p cell = q cell) :
    afterBoxes p outcome cell = afterBoxes q outcome cell := by
  cases outcome with
  | walk _ => exact same
  | push _ ending => cases ending <;> simp only [afterBoxes,change,same]
theorem selected_congr (p q : Pattern) (outcome : Outcome)
    (same : ∀ cell ∈ support, p cell = q cell) : selected p outcome = selected q outcome := by
  cases outcome with
  | walk _ =>
    unfold selected
    apply List.filter_congr
    intro cell member
    exact same cell member
  | push source _ =>
    unfold selected
    apply List.filter_congr
    intro cell member
    rw [same cell member]
theorem result_lift (phase hero : Nat) (p : Pattern) (outcome : Outcome)
    (small : Result phase hero (known (maskOf p)) outcome) : Result phase hero p outcome := by
  have agrees := known_agrees p
  have before := bonus_congr phase hero _ _ agrees
  have after := bonus_congr (nextPhase phase outcome) (nextHero outcome) _ _
    (fun cell member => after_agrees _ _ outcome cell (agrees cell member))
  have retained := selected_congr _ _ outcome agrees
  simpa only [Result,before,after,retained] using small
end NetHack.Soko11Sparse319
