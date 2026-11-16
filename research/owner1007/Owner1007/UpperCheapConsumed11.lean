import Owner1007.HeroEnergySubset11
import Owner1007.UpperBudget11
import Owner1007.TokenCounting
namespace Owner1007.UpperCheapConsumed11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem debts : U6.all (fun cell=>decide (value soko1_1.initial [cell]≤-6))=true := by decide +kernel

theorem singletons_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<6) :
 ∀ cell∈U6, endGroup [cell] outcomes=[] := by
 intro cell member
 apply Classical.byContradiction
 intro survives
 have inside : [cell]⊆U6 := by intro c found; have same : c=cell:=List.mem_singleton.mp found; exact same ▸ member
 have bound := energy_subset (Trace.nil soko1_1.initial) logged [cell] U6 (by simp) (by decide) inside (by decide) (by decide)
 have ledger := survivor_energy logged completed cell survives
 have debt := of_decide_eq_true (List.all_eq_true.mp debts cell member)
 have nonnegative : (0:Int)≤Int.ofNat (ownPushes [cell] outcomes) := Int.ofNat_nonneg _
 omega
#print axioms singletons_gone

theorem all_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<6) :
 endGroup U6 outcomes=[] := by
 have dead := singletons_gone logged completed cheap
 have count := logged.end_count_le (by decide) U6 (by decide) (by decide) (fun _=>false)
   (by intro cell member _; exact dead cell member)
 have filterEmpty : ∀ xs : List Cell, xs.filter (fun _=>false)=[] := by
   intro xs
   induction xs with
   | nil => rfl
   | cons c rest ih => simpa only [List.filter,Bool.false_eq_true,if_false] using ih
 rw [filterEmpty] at count
 have zero : (endGroup U6 outcomes).length=0 := by simp only [List.length_nil] at count; omega
 exact List.eq_nil_of_length_eq_zero zero
#print axioms all_gone
end Owner1007.UpperCheapConsumed11
