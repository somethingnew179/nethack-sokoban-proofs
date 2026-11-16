import Owner1007.RingEight12
import Owner1007.RingCageEleven12
import Owner1007.RingAfterTen12
import Owner1007.RingUpperTen12
import Owner1007.T291Eight12
import Owner1007.T239Ten12
namespace Owner1007.RingTen12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem ring_energy_ten
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 4}
 (hero : state.player∈PreCage12.ringRegion i) (inside : PreCage12.ringLocks i⊆group) :
 10≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good PreCage12.ring_closed PreCage12.ring_unique
   logged reached group gUnique subset hero inside with event|terminal
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
     obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
     have cases := RingSharpHeads12.classification j middle.player heroBefore dir source
       (PreRingHeads12.source_cases source dir pays) adjacent pays
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(PreCage12.ringLocks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (PreCage12.ring_unique j) locksOne owner smallShift
     rcases cases with blocked | cage | far | upper | sWest | tSouth | tBack | square
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := cage
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       have bound := RingCageEleven12.energy_eleven first checked effect last reached group gUnique subset j locksOne heroBefore completed
       change 11≤energy p group (before++(.push 263 (.stay 262))::after) at bound
       omega
     · obtain ⟨rfl,rfl⟩ := far
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 290 .west=[289] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact RingAfterTen12.energy_ten first checked effect last reached group gUnique subset j locksOne completed
     · obtain ⟨rfl,rfl⟩ := upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact RingUpperTen12.energy_ten first checked effect last reached group gUnique subset j locksOne heroBefore completed
     · obtain ⟨rfl,rfl⟩ := sWest
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       have activation : ∀ j, Quad29012.locks 0⊆211::(PreCage12.ringLocks j).erase 212 := by decide +kernel
       have kept := keep 211 (Quad29012.locks 0) (activation j)
       have heroNext : t.state.player∈Quad29012.region 0 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]
         decide +kernel
       have qActual := List.Subset.trans kept nextSubset
       have quad := Quad29012.energy_seven last nextReached (Quad29012.locks 0)
         (Quad29012.unique 0) qActual completed heroNext (fun _ h=>h)
       change 7≤energy p (Quad29012.locks 0) after at quad
       have upShift : ∀ j, CageLedger12.Upper⊆211::(PreCage12.ringLocks j).erase 212 := by decide +kernel
       have upInside := keep 211 CageLedger12.Upper (upShift j)
       have upActual := List.Subset.trans upInside nextSubset
       have upper := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
         (by decide +kernel) upActual completed
       have bonus : RightEnergy12.cert.bonus t.state.player
           (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push 212 (.stay 211)) effect]; decide +kernel
       rw [bonus] at upper
       change 2≤energy p CageLedger12.Upper after at upper
       have sum := TwoReserves12.add_le_energy last Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (Quad29012.locks 0) (update (endGroup group before) (.push 212 (.stay 211)))
         (by decide +kernel) nextUnique nextSubset (List.append_subset.mpr ⟨upInside,kept⟩)
       change energy p CageLedger12.Upper after+energy p (Quad29012.locks 0) after≤
         energy p (update (endGroup group before) (.push 212 (.stay 211))) after at sum
       have later : 9≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after := by omega
       have one : (2:Int)≤slack p (.push 212 (.stay 211)) := by decide +kernel
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega
     · obtain ⟨rfl,rfl⟩ := tSouth
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact T291Eight12.after_south265_ten first checked effect last reached group gUnique subset j locksOne heroBefore completed
     · obtain ⟨rfl,rfl⟩ := tBack
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 239 .south=[265] by decide +kernel) (by decide +kernel) checked effect
       subst ending
       rw [shape]
       exact T239Ten12.after_south239_ten first checked effect last reached group gUnique subset j locksOne heroBefore completed
     · have reserve (dest : Cell) (targets : pushTargets soko1_2.board source dir=[dest])
         (clear : dest∉soko1_2.initial.holes)
         (shift : [186,187,212,213]⊆dest::(PreCage12.ringLocks j).erase source) :
         10≤energy p group outcomes := by
         have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
           targets clear checked effect
         subst ending
         have kept := keep dest [186,187,212,213] shift
         have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
           (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
           [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
         change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push source (.stay dest))) after at later
         have amount : (10:Int)≤debtOf p [186,187,212,213] := by decide +kernel
         have nn := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
         change 0≤slack p (.push source (.stay dest)) at nn
         rw [shape,energy_at_split]
         simp only [projectedOutcome,if_pos owner]
         omega
       rcases square with ⟨rfl,rfl,shift⟩ | ⟨rfl,rfl,shift⟩
       · exact reserve 213 (by decide +kernel) (by decide +kernel) shift
       · exact reserve 212 (by decide +kernel) (by decide +kernel) shift
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (PreCage12.ring_unique j) (List.Subset.trans locksOne finalInside.2)
   rw [PreCage12.ring_size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms ring_energy_ten
end Owner1007.RingTen12

