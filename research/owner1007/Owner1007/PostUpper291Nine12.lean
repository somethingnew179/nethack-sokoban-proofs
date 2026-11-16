import Owner1007.RingUpperNine12
import Owner1007.Post187BareNine12
import Owner1007.Quad290Nine12
import Owner1007.UpperAfter187Bound12
import Owner1007.PostUpper291Data12
namespace Owner1007.PostUpper291Nine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.PostUpper29112
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem energy_nine {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 1}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 9≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩ := event.split
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset actualUnique group gUnique subset
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
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have cases := classification middle.player heroBefore dir (Geometry.all_directions dir) source pays adjacent
     have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(locks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (unique j) locksOne owner smallShift
     have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
       a+b≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega
     rcases cases with blocked | gateCase | high | sWest | main | tNorth | tSouth
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := gateCase
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 186 .west=[185] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 185 [158,159,185,210] gate
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 186 (.stay 185)) effect]; decide +kernel
       have later := CageLedger12.gate_owned_nineteen last nextReached
         (update (endGroup group before) (.push 186 (.stay 185))) nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 186 (.stay 185))) after at later
       have bound := reserve 2 19 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := high
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 161 .north=[135] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have all:∀j:Fin 1,VerticalPair12.pair false⊆135::(locks j).erase 161:=by decide +kernel
       have kept:=keep 135 (VerticalPair12.pair false) (all j)
       have heroNext:t.state.player∈VerticalPair12.region false 0:=by
         rw[matches_hero middle t (.push 161 (.stay 135)) effect]
         decide +kernel
       have later:=VerticalPair12.owned_energy_two false last nextReached _ nextUnique nextSubset heroNext kept
       change 2≤energy p (update (endGroup group before) (.push 161 (.stay 135))) after at later
       have bound:=reserve 8 2 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 211 (Quad29012.locks 0) quad
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]; decide +kernel
       have later := Quad290Nine12.energy_nine last nextReached
         (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset completed heroNext kept
       change 9≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
       have bound := reserve 2 9 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have all:∀j:Fin 1,Post187BareNine12.locks 0⊆262::(locks j).erase 263:=by decide +kernel
       have kept:=keep 262 (Post187BareNine12.locks 0) (all j)
       have heroNext : t.state.player∈Post187BareNine12.region 0 := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]; decide +kernel
       have later := Post187BareNine12.energy_nine last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset heroNext kept
       change 9≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have bound := reserve 2 9 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := tNorth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .north=[265] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := keep 265 (RingUpper12.locks 0) reset
       have heroNext : t.state.player∈RingUpper12.region 0 := by
         rw [matches_hero middle t (.push 291 (.stay 265)) effect]; decide +kernel
       have later := RingUpperNine12.energy_nine last nextReached
         (update (endGroup group before) (.push 291 (.stay 265))) nextUnique nextSubset completed heroNext kept
       change 9≤energy p (update (endGroup group before) (.push 291 (.stay 265))) after at later
       have bound := reserve 0 9 (by decide +kernel) later
       omega
     · obtain ⟨rfl,rfl⟩ := tSouth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 291 .south=[317] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have all : ∀ j : Fin 1, UpperAfter18712.locks 0⊆317::(locks j).erase 291 := by decide +kernel
       have kept := keep 317 (UpperAfter18712.locks 0) (all j)
       have heroNext : t.state.player∈UpperAfter18712.region 0 := by
         rw [matches_hero middle t (.push 291 (.stay 317)) effect]; decide +kernel
       have later := UpperAfter18712.owned_energy_two UpperAfter18712.matrix last nextReached
         (update (endGroup group before) (.push 291 (.stay 317))) nextUnique nextSubset heroNext kept
       change 2≤energy p (update (endGroup group before) (.push 291 (.stay 317))) after at later
       have bound := reserve 7 2 (by decide +kernel) later
       omega
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   have size : ∀ j, (locks j).length=12 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_nine
end Owner1007.PostUpper291Nine12
