import NetHack.Soko31Sparse134.Base
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPhaseCountedCorrection (afterBoxes nextPhase)

def maskOf (p : Pattern) : Nat :=
  (if p 177 then 1 else 0) + (if p 206 then 2 else 0) + (if p 207 then 4 else 0)
theorem mask_bound (p : Pattern) : maskOf p < 8 := by
  cases a : p 177 <;> cases b : p 206 <;> cases c : p 207 <;> simp [maskOf,a,b,c]
theorem known_agrees (p : Pattern) (cell : Cell) (member : cell ∈ support) :
    known (maskOf p) cell = p cell := by
  simp only [support, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals cases a : p 177 <;> cases b : p 206 <;> cases c : p 207 <;> simp [maskOf,known,a,b,c] <;> decide +kernel
theorem known_subset (p : Pattern) (cell : Cell) (selected : known (maskOf p) cell = true) :
    p cell = true := by
  by_cases a : cell = 177
  · subst cell; exact (known_agrees p 177 (by simp [support])).symm.trans selected
  by_cases b : cell = 206
  · subst cell; exact (known_agrees p 206 (by simp [support])).symm.trans selected
  by_cases c : cell = 207
  · subst cell; exact (known_agrees p 207 (by simp [support])).symm.trans selected
  simp only [known, if_neg a, if_neg b, if_neg c] at selected
  cases selected

theorem bonus_congr (phase hero : Nat) (p q : Pattern)
    (a : p 177 = q 177) (b : p 206 = q 206) (c : p 207 = q 207) :
    bonus phase hero p = bonus phase hero q := by simp only [bonus,a,b,c]
theorem after_agrees (p q : Pattern) (outcome : Outcome) (cell : Cell) (same : p cell = q cell) :
    afterBoxes p outcome cell = afterBoxes q outcome cell := by
  cases outcome with
  | walk _ => exact same
  | push _ ending => cases ending <;> simp only [afterBoxes,change,same]
theorem result_lift (phase hero : Nat) (p : Pattern) (outcome : Outcome)
    (small : Result phase hero (known (maskOf p)) outcome) : Result phase hero p outcome := by
  have a := known_agrees p 177 (by simp [support])
  have b := known_agrees p 206 (by simp [support])
  have c := known_agrees p 207 (by simp [support])
  have before := bonus_congr phase hero _ _ a b c
  have after := bonus_congr (nextPhase phase outcome) (nextHero outcome) _ _
    (after_agrees _ _ outcome 177 a) (after_agrees _ _ outcome 206 b) (after_agrees _ _ outcome 207 c)
  rcases small with monotone | pay
  · exact Or.inl (by simpa only [before,after] using monotone)
  · apply Or.inr
    cases outcome with
    | walk _ => exact pay
    | push source ending => cases ending <;> simpa only [Pay,b,c] using pay
end NetHack.Soko31Sparse134
