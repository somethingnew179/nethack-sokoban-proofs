import NetHack.Soko11PairCandidate321.C14Cover00
import NetHack.Soko11PairCandidate321.C14Cover01
import NetHack.Soko11PairCandidate321.C14Cover02
import NetHack.Soko11PairCandidate321.C14Cover03
import NetHack.Soko11PairCandidate321.C14Cover04
import NetHack.Soko11PairCandidate321.C14Cover05
import NetHack.Soko11PairCandidate321.C14Cover06
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked_coverage14 : coverageCheck14 = true := by
  have split : NetHack.Soko11Hero315.phases.crates 14 = ((NetHack.Soko11Hero315.phases.crates 14).drop 0 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 16 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 32 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 48 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 64 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 80 |>.take 16) ++ ((NetHack.Soko11Hero315.phases.crates 14).drop 96 |>.take 16) := by decide +kernel
  unfold coverageCheck14
  rw [split]
  simp only [List.all_append,checked14slice00,checked14slice01,checked14slice02,checked14slice03,checked14slice04,checked14slice05,checked14slice06,Bool.true_and]
theorem covered_positive14 (hero : Cell) (group : List Cell) (unique : group.Nodup)
    (inside : group ⊆ NetHack.Soko11Hero315.phases.crates 14) (positive : 0 < bonus 14 hero group) :
    ∃ pair ∈ positivePairs14, group.Perm pair := by
  have two : group.length = 2 := by
    by_cases h : group.length = 2
    · exact h
    · simp [bonus,h] at positive
  cases group with
  | nil => simp at two
  | cons a tail =>
    cases tail with
    | nil => simp at two
    | cons b rest =>
      cases rest with
      | nil =>
        have different : a ≠ b := by simpa using (List.nodup_cons.mp unique).1
        have all := checked_coverage14
        unfold coverageCheck14 coverageRow14 at all
        have x := List.all_eq_true.mp (List.all_eq_true.mp all a (inside (by simp))) b (inside (by simp))
        have choices := of_decide_eq_true x
        rcases choices with same|zero|forward|backward
        · exact False.elim (different same)
        · have impossible : bonus 14 hero [a,b] = 0 := by simp [bonus,tables,zero]
          rw [impossible] at positive
          omega
        · exact ⟨[a,b],forward,List.Perm.refl _⟩
        · exact ⟨[b,a],backward,List.Perm.swap b a []⟩
      | cons c rest => simp only [List.length_cons] at two; omega
end NetHack.Soko11PairCandidate321
