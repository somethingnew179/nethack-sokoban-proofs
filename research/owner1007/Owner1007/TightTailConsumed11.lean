import Owner1007.TightSurvivors11
import Owner1007.LoggedAppend11
namespace Owner1007.TightTailConsumed11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem gone {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤325)
 (group : List Cell) (unique : (group++[315,321]).Nodup) (inside : group⊆state.boulders) :
 endGroup group outcomes=[] := by
 let full := first.append tail
 obtain ⟨fixed315,fixed321⟩ := TightSurvivors11.stationary_zero_survivors full completed cheap
 have tag (cell : Cell) (zero : ownPushes [cell] (before++outcomes)=0) :
   endGroup [cell] before=[cell] ∧endGroup [cell] outcomes=[cell] := by
  rw [ownPushes_append] at zero
  have zeroBefore : ownPushes [cell] before=0 := by omega
  have beforeTag := no_push_unchanged [cell] before zeroBefore
  rw [beforeTag] at zero
  have zeroTail : ownPushes [cell] outcomes=0 := by omega
  exact ⟨beforeTag,no_push_unchanged [cell] outcomes zeroTail⟩
 have tag315 := tag 315 fixed315
 have tag321 := tag 321 fixed321
 have survivorInside : ([315,321] : List Cell)⊆state.boulders := by
  intro c member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·have selected := (first.end_subset (by decide) [315] (by decide) (by decide)).2
   exact selected (by rw [tag315.1];simp)
  ·have selected := (first.end_subset (by decide) [321] (by decide) (by decide)).2
   exact selected (by rw [tag321.1];simp)
 have actualUnique := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have survivors := HeroLedger.Logged.end_append_perm tail actualUnique [315] [321] (by decide) survivorInside
 rw [tag315.2,tag321.2] at survivors
 have survivorLength : (endGroup [315,321] outcomes).length=2 := survivors.length_eq
 have bothInside : group++[315,321]⊆state.boulders := List.append_subset.mpr ⟨inside,survivorInside⟩
 have selected := tail.end_subset actualUnique (group++[315,321]) unique bothInside
 have bothPerm := HeroLedger.Logged.end_append_perm tail actualUnique group [315,321] unique bothInside
 have bothUnique := bothPerm.nodup_iff.mp selected.1
 have actualInside : endGroup group outcomes++endGroup [315,321] outcomes⊆final.boulders :=
  fun _ h=>selected.2 (bothPerm.mem_iff.mpr h)
 have count := List.Nodup.length_le_of_subset bothUnique actualInside
 rw [List.length_append,survivorLength] at count
 have conservation := full.trace.conservation
 have empty : final.holes=[] := completed
 rw [empty] at conservation
 change 18+0=final.boulders.length+16 at conservation
 have zeroLength : (endGroup group outcomes).length=0 := by omega
 exact List.length_eq_zero_iff.mp zeroLength
#print axioms gone
end Owner1007.TightTailConsumed11
