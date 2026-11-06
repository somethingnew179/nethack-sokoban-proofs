/- Universal single-step simulation from reached ORIGINAL states. Selected
boulders remain a distinct subset of actual boulders. Costs are bounded by
the original scalar slack, including consuming rolling pushes. -/
import NetHack.Soko32Penalty5.ActionFacts
import NetHack.Soko32Penalty5.TransferTools
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.LowerBounds

theorem original_step {history : List Dir} {state : State} {pushes moves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state pushes moves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (dir : Dir) (t : Transition) (checked : step soko3_2.board state dir = some t) :
    ∃ after cost, Edge actions group state.player after t.state.player cost ∧
      after.Nodup ∧ after ⊆ t.state.boulders ∧
      potential.value state + Int.ofNat cost ≤ Int.ofNat t.pushCost + potential.value t.state := by
  have base := Generated.soko3_2_potential_valid.stepBound state dir t checked
  change potential.value state ≤ Int.ofNat t.pushCost + potential.value t.state at base
  rcases step_cases_full soko3_2.board state dir t checked with walked | pushed
  · rcases walked with ⟨target,adjacent,floor,clear,_,shape⟩
    have ghost := walking_of_step state group subset dir t checked target adjacent floor
      (fun h => clear (subset h))
    refine ⟨group,0,?_,unique,?_,?_⟩
    · simpa only [shape] using Edge.walk (actions := actions) ghost
    · simpa only [shape] using subset
    · change potential.value state + (0 : Int) ≤ _
      omega
  · rcases pushed with ⟨source,result,adjacent,floor,present,push,shape⟩
    by_cases owner : source ∈ group
    · obtain ⟨phase,other,res,active,holes,adjacent2,push2,_,covered⟩ :=
        NetHack.Soko32SAT.Frames.original_push_covered reached dir t checked (by simp only [shape])
      have eqSource := Option.some.inj (adjacent.symm.trans adjacent2)
      subst other
      have eqResult := Option.some.inj (push.symm.trans push2)
      subst res
      have erases := erase_subset subset unique source
      rcases (pushBoulder_spec soko3_2.board state source dir result push).1 with stay | fill
      · obtain ⟨unfilled,boxes⟩ := stay
        have cover : NetHack.Soko32SAT.Frames.Covered phase state.player source dir (.stay result.landing) := by
          simpa only [ending,unfilled] using covered
        obtain ⟨row,member,heroEq,sourceEq,_,landingEq⟩ := cover
        obtain ⟨a,actionMember,aHero,aSource,aLanding,aCost⟩ := stay_action row member
        have hero : a.hero = state.player := aHero.trans heroEq
        have src : a.source = source := aSource.trans sourceEq
        have land : a.landing = some result.landing := aLanding.trans (congrArg some landingEq)
        have different : result.landing ≠ source := by
          simpa only [landingEq,sourceEq] using stays_different row member
        have clear : result.landing ∉ state.boulders :=
          (NonlinearFacts.pushBoulder_landing_old_clear_or_source soko3_2.board state source dir result push).resolve_left different
        have legal : a.enabled group state.player := by
          simp only [Action.enabled,hero,src,land]
          exact ⟨by trivial,owner,fun h => clear (subset h)⟩
        have afterUnique : (a.after group).Nodup := by
          simp only [Action.after,land,src]
          split
          · exact unique.erase source
          · exact List.nodup_cons.mpr ⟨fun h => clear (subset (List.mem_of_mem_erase h)),unique.erase source⟩
        have afterSubset : a.after group ⊆ t.state.boulders := by
          rw [shape]
          simp only [Action.after,land,src,boxes]
          split
          · exact fun _ h => List.mem_cons_of_mem _ (erases h)
          · exact List.cons_subset_cons _ erases
        have effect : Matches state t (.push source (.stay result.landing)) := by
          refine ⟨present,?_⟩
          simpa only [unfilled,boxes,afterFill] using shape
        have delta := matches_delta potential state t _ effect
        have cost : Int.ofNat a.cost = slack potential (.push source (.stay result.landing)) := by
          simpa only [slack,landingEq,sourceEq] using aCost
        refine ⟨a.after group,a.cost,?_,afterUnique,afterSubset,?_⟩
        · simpa only [shape,src] using Edge.push (boxes := group) a actionMember legal
        · rw [cost]; exact Int.le_of_eq delta
      · obtain ⟨filled,hazard,boxes⟩ := fill
        have cover : NetHack.Soko32SAT.Frames.Covered phase state.player source dir (.fill result.landing) := by
          simpa only [ending,filled] using covered
        obtain ⟨heroEq,sourceEq,_,holeEq⟩ := cover
        let a := fillAction
        have legal : a.enabled group state.player := by
          change state.player = 269 ∧ 270 ∈ group ∧ True
          exact ⟨heroEq,sourceEq ▸ owner,True.intro⟩
        have afterSubset : a.after group ⊆ t.state.boulders := by
          simpa only [a,fillAction,Action.after,←sourceEq,shape,boxes] using erases
        have afterUnique : (a.after group).Nodup := by
          change (group.erase 270).Nodup; exact unique.erase _
        have effect : Matches state t (.push source (.fill result.landing)) := by
          refine ⟨present,hazard,?_⟩
          simpa only [filled,boxes,afterFill] using shape
        have delta := matches_delta potential state t _ effect
        have cost : Int.ofNat a.cost = slack potential (.push source (.fill result.landing)) := by
          change (0 : Int) = slack potential (.push source (.fill result.landing))
          simpa only [slack,sourceEq,holeEq] using fill_cost ⟨phase,active⟩
        refine ⟨a.after group,a.cost,?_,afterUnique,afterSubset,?_⟩
        · simpa only [shape,a,fillAction,sourceEq] using Edge.push (boxes := group) a fill_member legal
        · rw [cost]; exact Int.le_of_eq delta
    · have ghost := walking_of_step state group subset dir t checked source adjacent floor owner
      have erases : group ⊆ state.boulders.erase source := by
        intro c member
        have different : c ≠ source := by intro same; subst c; exact owner member
        exact (List.mem_erase_of_ne different).mpr (subset member)
      have nextSubset : group ⊆ t.state.boulders := by
        rw [shape]
        rcases (pushBoulder_spec soko3_2.board state source dir result push).1 with stay | fill
        · rw [stay.2]; exact fun _ h => List.mem_cons_of_mem _ (erases h)
        · rw [fill.2.2]; exact erases
      refine ⟨group,0,?_,unique,nextSubset,?_⟩
      · simpa only [shape] using Edge.walk (actions := actions) ghost
      · change potential.value state + (0 : Int) ≤ _
        omega

end NetHack.Soko32Penalty5
