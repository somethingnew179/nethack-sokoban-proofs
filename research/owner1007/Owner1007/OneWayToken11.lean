import Owner1007.HeroLedger
namespace Owner1007.OneWayToken11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

def AvoidLanding (cell : Cell) (group : List Cell) : Outcome → Prop
  | .push source (.stay landing) => source ∈ group → landing ≠ cell
  | _ => True

def NoReturn (cell : Cell) (group : List Cell) : List Outcome → Prop
  | [] => True
  | outcome :: rest => AvoidLanding cell group outcome ∧ NoReturn cell (update group outcome) rest

theorem backward (cell : Cell) (group : List Cell) (outcome : Outcome)
    (unique : group.Nodup) (avoid : AvoidLanding cell group outcome)
    (present : cell ∈ update group outcome) :
    cell ∈ group ∧ ownPush [cell] outcome = 0 ∧ update [cell] outcome = [cell] := by
  cases outcome with
  | walk target => exact ⟨present,rfl,rfl⟩
  | push source result =>
    by_cases owner : source ∈ group
    · cases result with
      | stay landing =>
        have after : cell ∈ landing :: group.erase source := by
          simpa only [update,move,if_pos owner,post] using present
        have erased : cell ∈ group.erase source := by
          rcases List.mem_cons.mp after with same | member
          · exact False.elim (avoid owner same.symm)
          · exact member
        have parts := unique.mem_erase_iff.mp erased
        have notOwner : source ∉ [cell] := by simp only [List.mem_singleton]; exact parts.1.symm
        refine ⟨parts.2,?_,?_⟩ <;> simp only [ownPush,update,move,if_neg notOwner]
      | fill hole =>
        have erased : cell ∈ group.erase source := by
          simpa only [update,move,if_pos owner,post] using present
        have parts := unique.mem_erase_iff.mp erased
        have notOwner : source ∉ [cell] := by simp only [List.mem_singleton]; exact parts.1.symm
        refine ⟨parts.2,?_,?_⟩ <;> simp only [ownPush,update,move,if_neg notOwner]
    · have before : cell ∈ group := by simpa only [update,move,if_neg owner] using present
      have notOwner : source ∉ [cell] := by
        simp only [List.mem_singleton]
        intro same
        exact owner (same ▸ before)
      refine ⟨before,?_,?_⟩ <;> simp only [ownPush,update,move,if_neg notOwner]

theorem historical {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (cell : Cell) (group : List Cell)
    (unique : group.Nodup) (inside : group ⊆ initial.boulders)
    (quiet : NoReturn cell group outcomes) (present : cell ∈ endGroup group outcomes) :
    cell ∈ group ∧ ownPushes [cell] outcomes = 0 := by
  induction logged generalizing group with
  | nil state => exact ⟨present,rfl⟩
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextActual := step_boulders_nodup board state dir t actualUnique head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
    have nextInside := GhostSubset.update_subset state t outcome effect group unique inside
    obtain ⟨nextPresent,tailZero⟩ := ih nextActual (update group outcome) nextUnique nextInside quiet.2 present
    obtain ⟨oldPresent,headZero,same⟩ := backward cell group outcome unique quiet.1 nextPresent
    refine ⟨oldPresent,?_⟩
    simp only [ownPushes,headZero,same,tailZero,Nat.zero_add]

#print axioms historical
end Owner1007.OneWayToken11
