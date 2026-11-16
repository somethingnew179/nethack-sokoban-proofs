import Owner1007.ResidualBoost12
import Owner1007.FarRingSeven12
import Owner1007.Quad289Bound12
import Owner1007.Quad211Trap12
import Owner1007.RingPrepared12
namespace Owner1007.Quad290Nine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks (_ : Fin 1) : List Cell := [210,211,237,263,290]
def region (_ : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c => !([236,262,288,289,210,211,237,263,290] : List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210 ∧ dir=.south) ∨ (source=237 ∧ dir=.west) ∨
 (source=263 ∧ dir=.west) ∨ (source=290 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem main {source dir} (h : paid source dir) : RingCut12.paid source dir := h

theorem energy_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player∈region 0) (inside : locks 0⊆group) :
 9≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have initialUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩ := event.split
   have only : j=0 := Subsingleton.elim j 0
   subst j
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset initialUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
       (NorthBound12.ring_priced source dir (main pays)) checked effect
     have reserve (later : (7:Int)≤energy p (update (endGroup group before) (.push source ending)) after) :
       9≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(locks 0).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (unique 0) locksOne owner smallShift
     rcases pays with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
     · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 236 (ResidualBoost12.locks 0) (by decide +kernel)
       have heroNext : t.state.player∈ResidualBoost12.region 0 := by
         rw [matches_hero middle t (.push 210 (.stay 236)) effect]
         decide +kernel
       have later := ResidualBoost12.owned_credit last nextReached
         (update (endGroup group before) (.push 210 (.stay 236))) nextUnique nextSubset 0 heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 210 (.stay 236))) after at later
       exact reserve later
     · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 236 [210,236] (by decide +kernel)
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 237 (.stay 236))) nextUnique nextSubset
         [210,236] CageLedger12.locked_210236 (by decide +kernel) kept
       change debtOf p [210,236]≤energy p (update (endGroup group before) (.push 237 (.stay 236))) after at later
       have amount : (7:Int)≤debtOf p [210,236] := by decide +kernel
       exact reserve (by omega)
     · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Quad211Trap12.locks 0) (by decide +kernel)
       have heroNext : t.state.player∈Quad211Trap12.region 0 := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         decide +kernel
       have later := Quad211Trap12.owned_energy_fifteen last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset heroNext kept
       change 15≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       exact reserve (by omega)
     · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 289 (FarRingSeven12.C) (by decide +kernel)
       have heroNext : t.state.player∈FarRingSeven12.region 0 := by
         rw [matches_hero middle t (.push 290 (.stay 289)) effect]
         decide +kernel
       have later := FarRingSeven12.owned_seven last nextReached
         (update (endGroup group before) (.push 290 (.stay 289))) nextUnique nextSubset completed heroNext kept
       change 7≤energy p (update (endGroup group before) (.push 290 (.stay 289))) after at later
       exact reserve later
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have only : j=0 := Subsingleton.elim j 0
   subst j
   have finalInside := logged.end_subset initialUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique 0) (List.Subset.trans locksOne finalInside.2)
   change 5≤final.boulders.length at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_nine
end Owner1007.Quad290Nine12

