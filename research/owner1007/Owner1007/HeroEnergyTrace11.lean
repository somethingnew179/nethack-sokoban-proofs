import Owner1007.HeroEnergyPartitions11
import Owner1007.TokenPersistence
import Owner1007.LockedTokens
namespace Owner1007.Hero315Frame11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

theorem charges_append (credits : Cell → Int) (group : List Cell) (first second : List Outcome) :
 HeroLedger.charges credits group (first ++ second) =
 HeroLedger.charges credits group first + HeroLedger.charges credits (endGroup group first) second := by
 induction first generalizing group with
 | nil => simp only [List.nil_append,HeroLedger.charges,endGroup,Int.zero_add]
 | cons outcome rest ih =>
   simp only [List.cons_append,HeroLedger.charges,endGroup,ih]
   omega

theorem energy_append (initial middle final : State) (group : List Cell) (first second : List Outcome) :
 energy initial final group (first ++ second) = energy initial middle group first +
   energy middle final (endGroup group first) second := by
 unfold energy HeroLedger.energy
 rw [charges_append,endGroup_append]
 omega

theorem prefix_energy_le {beforeDirs middle beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (last : Logged soko1_1.board middle afterDirs final afterPushes afterMoves after)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆soko1_1.initial.boulders) :
 energy soko1_1.initial middle group before ≤ energy soko1_1.initial final group (before++after) := by
 have selected := first.end_subset (by decide +kernel) group unique inside
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have bound := endGroup_length_le group before
 have initialBound := List.Nodup.length_le_of_subset unique inside
 change group.length≤18 at initialBound
 have tailNN := HeroLedger.Logged.energy_nonnegative last (groupCertificate 18) valid
   (endGroup group before) selected.1 selected.2 (by omega)
 change 0≤energy middle final (endGroup group before) after at tailNN
 have split := energy_append soko1_1.initial middle final group before after
 omega

theorem ownPushes_append (group : List Cell) (first second : List Outcome) :
 ownPushes group (first++second) = ownPushes group first + ownPushes (endGroup group first) second := by
 induction first generalizing group with
 | nil => simp only [List.nil_append,ownPushes,endGroup,Nat.zero_add]
 | cons outcome rest ih =>
   simp only [List.cons_append,ownPushes,endGroup,ih]
   omega

theorem locked_identity {board state dirs final pushes moves outcomes locks cell}
 (logged : Logged board state dirs final pushes moves outcomes)
 (locked : Owner1007.Locked board locks) (inside : locks⊆state.boulders) (member : cell∈locks) :
 endGroup [cell] outcomes=[cell] := by
 induction logged with
 | nil => rfl
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   have nextInside := Owner1007.locked_step locked inside head
   have unchanged : update [cell] outcome=[cell] := by
     cases outcome with
     | walk _ => rfl
     | push source ending =>
       have absent := locked_push_outside locked inside head effect
       have different : source≠cell := by intro same; exact absent (same ▸ member)
       have notOwn : source∉[cell] := by simpa only [List.mem_singleton] using different
       simp only [update,move,if_neg notOwn]
   simpa only [endGroup,unchanged] using ih nextInside

#print axioms energy_append
#print axioms prefix_energy_le
#print axioms ownPushes_append
#print axioms locked_identity
end Owner1007.Hero315Frame11
