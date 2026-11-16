import Owner1007.LeftSplitFour11
namespace Owner1007.LeftSplitEight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.LeftSplit11
theorem eight_of_split {state final : State}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after)
 (completed : Goal final)
 (same : (endGroup [186,212] before).Perm [185,211]) (hero : state.player∈region 0)
 (cash : 2≤PaidCount11.count LeftPair11.paid [186,212] beforeDirs before) :
 8≤energy soko1_1.initial final [186,212] (before++after) := by
 by_cases enough : 8≤energy soko1_1.initial final [186,212] (before++after)
 · exact enough
 · have cheap : energy soko1_1.initial final [186,212] (before++after)<8 := by omega
   let logged := first.append last
   have gone : endGroup [186,212] (before++after)=[] := by
     have dead : ∀c∈([186,212] : List Cell), endGroup [c] (before++after)=[] := by
       intro c member
       apply Classical.byContradiction
       intro survives
       have sub : [c]⊆([186,212] : List Cell) := by
         intro x h
         have eq : x=c := List.mem_singleton.mp h
         exact eq ▸ member
       have bound := energy_subset (Trace.nil soko1_1.initial) logged [c] [186,212] (by simp) (by decide)
         sub (by decide) (by decide)
       have ledger := survivor_energy logged completed c survives
       have debt : value soko1_1.initial [c]≤-8 := by
         rcases List.mem_cons.mp member with rfl|later
         · decide +kernel
         · have eq : c=212:=List.mem_singleton.mp later
           subst c; decide +kernel
       have nn : (0:Int)≤Int.ofNat (ownPushes [c] (before++after)) := Int.natCast_nonneg _
       omega
     have count := logged.end_count_le (by decide) [186,212] (by decide) (by decide) (fun _=>false)
       (by intro c h _; exact dead c h)
     have zero : ([186,212].filter fun _=>false : List Cell)=[] := rfl
     rw [zero] at count
     exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at count; omega)
   have facts := first.end_subset (by decide) [186,212] (by decide) (by decide)
   have bounded := endGroup_length_le [186,212] before
   change (endGroup [186,212] before).length≤2 at bounded
   have currentGone : endGroup (endGroup [186,212] before) after=[] := by rw [←endGroup_append]; exact gone
   have good : OwnedCorral11.Good locks region state (endGroup [186,212] before) :=
     ⟨0,hero,fun c h=>same.mem_iff.mpr h⟩
   have tail := LeftSplitFour11.future_four first.trace last _ facts.1 facts.2 same hero currentGone
   have prefixBound := PaidCount11.energy_bound priced first NetHack.SokobanLinearPhases.Map11.initial_good
     [186,212] (by decide) (by decide) (by decide)
   have split := energy_append soko1_1.initial state final [186,212] before after
   simp only [Int.ofNat_eq_natCast] at prefixBound
   omega

#print axioms eight_of_split
end Owner1007.LeftSplitEight11
