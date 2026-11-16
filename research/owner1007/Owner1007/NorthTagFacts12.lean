import Owner1007.PreCageFacts12
import Owner1007.TokenAccounting
namespace Owner1007.NorthTagFacts12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007 Owner1007.TokenAccounting Owner1007.PreCage12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def fixed : List Cell := U ++ [210,237,238,263,265,318]
def selected : List Cell := fixed ++ [213,345]
def UP : List Cell := U ++ [213]

theorem tag_inside : ∀ i, northS i∈northLocks i ∧ northTag i∈northLocks i := by decide +kernel

theorem tag_update : ∀ i source dir j dest, northAllowed i source dir j dest →
    update [northS i] (.push source (.stay dest))=[northS j] ∧
    update [northTag i] (.push source (.stay dest))=[northTag j] := by
  have s : ∀ i j : Fin 10, northS i=213 → j.val=i.val+1 →
      update [northS i] (.push 213 (.stay 212))=[northS j] ∧
      update [northTag i] (.push 213 (.stay 212))=[northTag j] := by decide +kernel
  have t345 : ∀ i j : Fin 10, northTag i=345 → j.val=i.val+2 →
      update [northS i] (.push (northTag i) (.stay 319))=[northS j] ∧
      update [northTag i] (.push (northTag i) (.stay 319))=[northTag j] := by decide +kernel
  have t319 : ∀ i j : Fin 10, northTag i=319 → j.val=i.val+2 →
      update [northS i] (.push (northTag i) (.stay 293))=[northS j] ∧
      update [northTag i] (.push (northTag i) (.stay 293))=[northTag j] := by decide +kernel
  have t293 : ∀ i j : Fin 10, northTag i=293 → j.val=i.val+2 →
      update [northS i] (.push (northTag i) (.stay 292))=[northS j] ∧
      update [northTag i] (.push (northTag i) (.stay 292))=[northTag j] := by decide +kernel
  have t292 : ∀ i j : Fin 10, northTag i=292 → j.val=i.val+2 →
      update [northS i] (.push (northTag i) (.stay 291))=[northS j] ∧
      update [northTag i] (.push (northTag i) (.stay 291))=[northTag j] := by decide +kernel
  intro i source dir j dest allowed
  rcases allowed with ⟨at213,rfl,rfl,step,rfl⟩ | ⟨step,rfl,which⟩
  · exact s i j at213 step
  · rcases which with ⟨at345,rfl,rfl⟩ | ⟨at319,rfl,rfl⟩ | ⟨at293,rfl,rfl⟩ | ⟨at292,rfl,rfl⟩
    · exact t345 i j at345 step
    · exact t319 i j at319 step
    · exact t293 i j at293 step
    · exact t292 i j at292 step

theorem fixed_inside : ∀ i, fixed⊆northLocks i := by decide +kernel
theorem tag_away : ∀ i, northTag i∉fixed := by decide +kernel
theorem fixed_guard : ∀ i hero, hero∈northRegion i → ∀ dir source, source∈fixed →
    advance soko1_2.board hero dir=some source →
    BlockedPush soko1_2.board (northLocks i) source dir ∨ northPaid source dir := by
  intro i hero inside dir source member adjacent
  rcases north_tag_sound i hero inside source (fixed_inside i member) dir adjacent with blocked | paid | shifted
  · exact Or.inl blocked
  · exact Or.inr paid
  · obtain ⟨j,dest,_,_,_,_,_,allowed⟩ := shifted
    rcases allowed with h | h
    · obtain ⟨_,at213,_,_,_⟩ := h
      have absent : (213 : Cell)∉fixed := by decide +kernel
      exact False.elim (absent (at213 ▸ member))
    · obtain ⟨_,atTag,_⟩ := h
      exact False.elim ((tag_away i) (atTag ▸ member))

theorem s_only : ∀ i, ∀ source∈([213,212] : List Cell),
    source∈northLocks i → source=northS i := by decide +kernel
theorem blocked_s_north : ∀ i, BlockedPush soko1_2.board (northLocks i) 212 .north := by decide +kernel
#print axioms tag_update
#print axioms fixed_guard
end Owner1007.NorthTagFacts12
