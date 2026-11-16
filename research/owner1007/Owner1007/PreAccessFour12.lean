import Owner1007.PreAccessFour12Data
import Owner1007.Foreign184UpperFour12
namespace Owner1007.PreAccessFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem energy_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 3}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 4≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays⟩ :=event.split
   have atReached := reached.append first.trace
   have old := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual _ old.1 old.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect _ old.1 old.2
   have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
   have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at nn
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,headPaid⟩:=pays
     have uBefore := List.Subset.trans (upper_inside j) locksHead
     have uMono := update_mono U (endGroup group before) (by decide +kernel) uBefore (.push source ending)
     have uSame : update U (.push source ending)=U := by
       simp only [update,move,if_neg (paid_outside headPaid)]
     rw [uSame] at uMono
     have uNext : U⊆update (endGroup group before) (.push source ending) := uMono
     have uPhysical := List.Subset.trans uNext nextSubset
     have whole : energy p group outcomes=ownSlack p group before+slack p (.push source ending)+
       energy p (update (endGroup group before) (.push source ending)) after := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
     have headNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     change 0≤slack p (.push source ending) at headNN
     rcases headPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|headPositive
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 210 .north=[184] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (foreign_shift j)
       change Foreign184UpperFour12.locks 0⊆update (endGroup group before) (.push 210 (.stay 184)) at kept
       have heroNext : t.state.player∈Foreign184UpperFour12.region 0 := by
         rw [matches_hero middle t (.push 210 (.stay 184)) effect]
         exact Foreign184UpperFour12.hero210
       have later := Foreign184UpperFour12.energy_four last nextReached _ nextUnique nextSubset completed heroNext kept
       change 4≤energy p (update (endGroup group before) (.push 210 (.stay 184))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 211 .north=[185] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (gate_shift j)
       have heroNext : t.state.player∈PriceTrap12Gate.region 0 := by
         rw [matches_hero middle t (.push 211 (.stay 185)) effect]
         exact gate_hero
       have later := CageLedger12.gate_owned_nineteen last nextReached _ nextUnique nextSubset heroNext kept
       change 19≤energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (pair_shift j)
       have heroNext : t.state.player∈Vertical21223812.region 0 := by
         rw [matches_hero middle t (.push 213 (.stay 212)) effect]
         exact pair_hero
       have pairPhysical := List.Subset.trans kept nextSubset
       have pair := Vertical21223812.owned_energy_two last nextReached [212,238] (by decide +kernel)
         pairPhysical heroNext (fun _ h=>h)
       change 2≤energy p [212,238] after at pair
       have upper := RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uPhysical completed
       have bonus : RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2 := by
         rw [matches_hero middle t (.push 213 (.stay 212)) effect]
         exact upper_bonus 213 (by decide +kernel)
       rw [bonus] at upper
       change 2≤energy p U after at upper
       have both : U++[212,238]⊆update (endGroup group before) (.push 213 (.stay 212)) :=
         List.append_subset.mpr ⟨uNext,kept⟩
       have sum := TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual U [212,238]
         (update (endGroup group before) (.push 213 (.stay 212))) (by decide +kernel) nextUnique nextSubset both
       change energy p U after+energy p [212,238] after≤energy p (update (endGroup group before) (.push 213 (.stay 212))) after at sum
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         (show pushTargets soko1_2.board 238 .north=[212] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have kept := CageFour12.shifted_inside (unique j) locksHead owner (square_shift j)
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push 238 (.stay 212))) nextUnique nextSubset
         [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
       change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push 238 (.stay 212))) after at later
       have debtBound : (4:Int)≤debtOf p [186,187,212,213] := by decide +kernel
       omega
     · have member := positive_member headPositive
       have price := push_effect_price p soko1_2.initial.holes 2 atReached.holes_sublist.subset
         (positive_price source member dir (Geometry.all_directions dir) headPositive) checked effect
       have upper := RightEnergy12.raw_group_energy last nextReached U (by decide +kernel) uPhysical completed
       have bonus : RightEnergy12.cert.bonus t.state.player (NetHack.Sokoban.PatternCorrection.project U)=2 := by
         rw [matches_hero middle t (.push source ending) effect]
         exact upper_bonus source (List.mem_cons_of_mem 213 member)
       rw [bonus] at upper
       change 2≤energy p U after at upper
       have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual U
         (update (endGroup group before) (.push source ending)) (by decide +kernel) nextUnique uPhysical nextSubset uNext
       change energy p U after≤energy p (update (endGroup group before) (.push source ending)) after at mono
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept finalInside.2)
   have huge := large j
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_four
end Owner1007.PreAccessFour12
