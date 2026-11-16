import Owner1007.TransportQuiet11
import Owner1007.PaidCount11
namespace Owner1007.QuietFromCount11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
theorem from_count {paid} [∀c d,Decidable (paid c d)] {state dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (zero : PaidCount11.count paid group dirs outcomes=0) :
 UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes := by
 induction logged generalizing group with
 |nil=>exact .nil _ _
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
  have noOwn : ¬PaidCount11.owned paid group dir outcome := by
   intro pays
   simp only [PaidCount11.count,if_pos pays] at zero
   omega
  have nextZero : PaidCount11.count paid (update group outcome) rest outcomes=0 := by
   simpa only [PaidCount11.count,if_neg noOwn,Nat.zero_add] using zero
  exact .cons head effect (fun pays=>noOwn ((PaidCount11.owned_iff effect).mpr pays)) (ih _ nextZero)

theorem from_two_counts {first second} [∀c d,Decidable (first c d)] [∀c d,Decidable (second c d)]
 {state dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (group : List Cell)
 (zeroFirst : PaidCount11.count first group dirs outcomes=0)
 (zeroSecond : PaidCount11.count second group dirs outcomes=0) :
 UpperQuiet11.Quiet (fun c d=>first c d∨second c d) state group dirs final pushes moves outcomes := by
 induction logged generalizing group with
 |nil=>exact .nil _ _
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
  have noFirst : ¬PaidCount11.owned first group dir outcome := by
   intro pays
   simp only [PaidCount11.count,if_pos pays] at zeroFirst
   omega
  have noSecond : ¬PaidCount11.owned second group dir outcome := by
   intro pays
   simp only [PaidCount11.count,if_pos pays] at zeroSecond
   omega
  have nextFirst : PaidCount11.count first (update group outcome) rest outcomes=0 := by
   simpa only [PaidCount11.count,if_neg noFirst,Nat.zero_add] using zeroFirst
  have nextSecond : PaidCount11.count second (update group outcome) rest outcomes=0 := by
   simpa only [PaidCount11.count,if_neg noSecond,Nat.zero_add] using zeroSecond
  have avoid : ¬OwnedCorral11.PaidStep (fun c d=>first c d∨second c d) group dir t := by
   rintro ⟨source,owner,metadata,pays⟩
   rcases pays with left|right
   ·exact noFirst ((PaidCount11.owned_iff effect).mpr ⟨source,owner,metadata,left⟩)
   ·exact noSecond ((PaidCount11.owned_iff effect).mpr ⟨source,owner,metadata,right⟩)
  exact .cons head effect avoid (ih _ nextFirst nextSecond)
#print axioms from_count
#print axioms from_two_counts
end Owner1007.QuietFromCount11
