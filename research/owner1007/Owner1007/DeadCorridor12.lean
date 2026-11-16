import Owner1007.LockedTokens
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.DeadCorridor12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def corridor : List Cell := [288,289,290,291,292,293,294]
theorem corridor_clear : ∀ c ∈ corridor, c ∉ soko1_2.initial.holes := by decide +kernel
theorem guard : ∀ hero ∈ soko1_2.board.floor, hero ≠ 317 → ∀ dir ∈ allDirs,
    ∀ source ∈ corridor, advance soko1_2.board hero dir = some source →
    BlockedPush soko1_2.board [317] source dir ∨ pushTargets soko1_2.board source dir ⊆ corridor := by decide +kernel

theorem effect_targets {board state dir t source ending}
    (checked : step board state dir = some t) (effect : Matches state t (.push source ending)) :
    match ending with
    | .stay landing => landing ∈ pushTargets board source dir
    | .fill hole => hole ∈ pushTargets board source dir := by
  have isPush : t.pushed = true := by
    cases ending with
    | stay landing => simp only [effect.2]
    | fill hole => simp only [effect.2.2]
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at isPush
    contradiction
  · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
    have srcEq : other=source := by
      cases ending with
      | stay landing =>
        have h := congrArg (fun x : Transition => x.state.player) effect.2
        simpa only [shape] using h
      | fill hole =>
        have h := congrArg (fun x : Transition => x.state.player) effect.2.2
        simpa only [shape] using h
    subst other
    have targets := (pushBoulder_spec board state source dir result push).2
    cases ending with
    | stay landing =>
      have h := congrArg Transition.landing effect.2
      have same : result.landing=landing := by simpa only [shape,Option.some.injEq] using h
      simpa only [same] using targets
    | fill hole =>
      have h := congrArg Transition.landing effect.2.2
      have same : result.landing=hole := by simpa only [shape,Option.some.injEq] using h
      simpa only [same] using targets

theorem ending_inside {state dir t source ending}
    (checked : step soko1_2.board state dir = some t)
    (effect : Matches state t (.push source ending))
    (park : 317 ∈ state.boulders) (member : source ∈ corridor) :
    match ending with | .stay c => c ∈ corridor | .fill c => c ∈ corridor := by
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  have physical := step_player_clear soko1_2.board state dir t checked
  have away : state.player ≠ 317 := by intro same; exact physical.2.2.1 (same ▸ park)
  rcases guard state.player physical.1 away dir (Geometry.all_directions dir) source member adjacent with blocked | stays
  · have first := push_first_clear soko1_2.board state source dir result push
    rcases blocked with diagonal | blocked
    · simp only [first.1] at diagonal
      contradiction
    · obtain ⟨dest,next,floor,door,empty⟩ := first.2
      simp only [next] at blocked
      rcases blocked with wall | door' | box
      · exact False.elim (wall floor)
      · exact False.elim (door door')
      · have same : dest=317 := List.mem_singleton.mp box
        exact False.elim (empty (same ▸ park))
  · have landing := effect_targets checked effect
    cases ending with
    | stay c => exact stays landing
    | fill c => exact stays landing

theorem trapped_survives {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    (park : 317 ∈ state.boulders) (holes : state.holes ⊆ soko1_2.initial.holes)
    (cell : Cell) (member : cell ∈ corridor) :
    endGroup [cell] outcomes ≠ [] := by
  induction logged generalizing cell with
  | nil current => simp [endGroup]
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextPark : 317 ∈ t.state.boulders := by
      have kept := locked_step dead317_locked (by intro c h; have same := List.mem_singleton.mp h; simpa only [same] using park) head
      exact kept (List.mem_cons_self)
    have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holes
    cases outcome with
    | walk target =>
      simpa only [endGroup,update] using ih nextPark nextHoles cell member
    | push source ending =>
      by_cases owns : source=cell
      · subst source
        have inside := ending_inside head effect park member
        cases ending with
        | stay landing =>
          simpa only [endGroup,update,move,List.mem_cons,List.not_mem_nil,or_false,if_true,
            post,List.erase_cons_head] using ih nextPark nextHoles landing inside
        | fill hole =>
          exact False.elim (corridor_clear hole inside (holes effect.2.1))
      · have absent : source ∉ [cell] := by simp [owns]
        simpa only [endGroup,update,move,if_neg absent] using ih nextPark nextHoles cell member
#print axioms trapped_survives
end Owner1007.DeadCorridor12

