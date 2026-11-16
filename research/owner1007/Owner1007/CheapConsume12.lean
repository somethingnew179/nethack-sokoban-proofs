import Owner1007.TokenCounting
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.CheapConsume12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
theorem cheap_group_consumed {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
 (subset : group⊆state.boulders)
 (debt : ∀ cell∈group, (5:Int)≤-p.boulder cell)
 (cheap : energy p group outcomes≤4) : endGroup group outcomes=[] := by
 have dead : ∀ cell∈group, endGroup [cell] outcomes=[] := by
   intro cell member
   apply Classical.byContradiction
   intro survives
   have ledger := survivor_energy p cell outcomes survives
   have bound := logged.member_energy_le Generated.soko1_2_potential_valid actualUnique group unique subset cell member
   change energy p [cell] outcomes≤energy p group outcomes at bound
   have initial := debt cell member
   simp only [Int.ofNat_eq_natCast] at ledger
   omega
 have count := logged.end_count_le actualUnique group unique subset (fun _ => false)
   (by intro cell member _; exact dead cell member)
 have filterEmpty : ∀ xs : List Cell, xs.filter (fun _ => false)=[] := by
   intro xs
   induction xs with
   | nil => rfl
   | cons c rest ih => simpa only [List.filter,Bool.false_eq_true,if_false] using ih
 rw [filterEmpty] at count
 have zero : (endGroup group outcomes).length=0 := by simp only [List.length_nil] at count; omega
 exact List.eq_nil_of_length_eq_zero zero
#print axioms cheap_group_consumed
end Owner1007.CheapConsume12

