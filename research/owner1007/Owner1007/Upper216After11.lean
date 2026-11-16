import Owner1007.UpperFirstCut11
import Owner1007.PostCuts11
namespace Owner1007.Upper216After11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem retained191_checked :
 (List.finRange 19).all (fun i => decide (216∉UpperZero11.locks i ∨ 191∈UpperZero11.locks i))=true := by
 decide +kernel

theorem FirstCut.after_216east {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (sourceEq : cut.actor.pushSource=some 216)
    (effect : Matches cut.middle cut.actor (.push 216 (.stay 217))) :
    [191,217] ⊆ update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome ∧
      OwnedCorral11.Good PostCuts11.rightLocks PostCuts11.rightRegion cut.actor.state [191,217] := by
  have good := quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
    original_good (by simp)
  obtain ⟨i,_,inside⟩ := good
  obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
  have same : source=216 := Option.some.inj (metadata.symm.trans sourceEq)
  have before216 : 216∈endGroup originalGroup cut.beforeOutcomes := same ▸ owner
  have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
  change (endGroup originalGroup cut.beforeOutcomes).length≤3 at bounded
  have locked := UpperQuiet11.lock_complete i (endGroup originalGroup cut.beforeOutcomes) bounded inside 216 before216
  have row := of_decide_eq_true (List.all_eq_true.mp retained191_checked i (by simp))
  have before191 : 191∈endGroup originalGroup cut.beforeOutcomes := inside (row.resolve_left (fun absent => absent locked))
  have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome
    (.push 216 (.stay 217)) cut.headEffect effect
  constructor
  · rw [headEq]
    simp only [update,move,if_pos before216,post]
    intro cell found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at found
    rcases found with rfl|rfl
    · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 191≠216)).mpr before191)
    · simp
  · refine ⟨⟨0,by decide⟩,?_,?_⟩
    · have hero : cut.actor.state.player=216 := by rw [effect.2]
      rw [hero]; decide +kernel
    · exact List.Subset.refl _

#print axioms FirstCut.after_216east
end Owner1007.Upper216After11
