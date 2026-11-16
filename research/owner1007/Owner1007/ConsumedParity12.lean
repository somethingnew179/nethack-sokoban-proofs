import Owner1007.ConsumedParity12Data
import NetHack.SokobanLinearPhases.Map12.Invariant
namespace Owner1007.ConsumedParity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem head_nonempty {board state dir t} (head : step board state dir=some t) : state.holes≠[] := by
 intro empty
 have stopped : step board state dir=none := by
   rcases state with ⟨player,boulders,remaining⟩
   cases empty
   cases standing : standingAllowed board ⟨player,boulders,[]⟩ <;>
     simp only [step,standing,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,bind,pure,Option.bind_some] <;> rfl
 rw [stopped] at head
 contradiction

theorem active_crates {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map12.certificate state)
 (nonempty : state.holes≠[]) : state.boulders⊆crates := by
 obtain ⟨phase,bound,holes,hero,boxes⟩ := valid.2
 have active : phase<18 := by
   change phase≤18 at bound
   by_cases active : phase<18
   ·exact active
   ·have same : phase=18 := by omega
    have empty : state.holes=[] := by
      rw [same,show soko1_2.initial.holes.drop 18=[] by decide +kernel] at holes
      exact holes
    exact False.elim (nonempty empty)
 have checked := List.all_eq_true.mp phase_checked phase (List.mem_range.mpr active)
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp checked c (boxes member))

theorem stay_geometry {board : Board} {state : State} {dir : Dir} {t : Transition} {source landing : Cell}
    (checked : step board state dir = some t)
    (effect : Matches state t (.push source (.stay landing))) :
    dir.diagonal=false ∧ landing ∈ pushTargets board source dir := by
  have sourceEq : t.pushSource=some source := by rw [effect.2]
  rcases step_cases_full _ _ _ _ checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at sourceEq
    contradiction
  · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
    have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
    subst other
    have landingEq : result.landing=landing := by
      have eq : t.landing=some landing := by rw [effect.2]
      simpa only [shape,Option.some.injEq] using eq
    exact ⟨(push_first_clear _ _ _ _ _ push).1,by simpa only [landingEq] using (pushBoulder_spec _ _ _ _ _ push).2⟩

theorem fill_geometry {board : Board} {state : State} {dir : Dir} {t : Transition} {source hole : Cell}
 (checked : step board state dir=some t)
 (effect : Matches state t (.push source (.fill hole))) :
 hole∈pushTargets board source dir := by
 have sourceEq : t.pushSource=some source := by rw [effect.2.2]
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at sourceEq
   contradiction
 · obtain ⟨other,result,_,_,_,push,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
   subst other
   have landingEq : result.landing=hole := by
     have eq : t.landing=some hole := by rw [effect.2.2]
     simpa only [shape,Option.some.injEq] using eq
   simpa only [landingEq] using (pushBoulder_spec _ _ _ _ _ push).2

theorem one_even {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {dirs final pushes moves outcomes}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map12.certificate state)
 (head : step soko1_2.board state dir=some t) (effect : Matches state t outcome)
 (tail : Logged soko1_2.board t.state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (inside : group⊆state.boulders) :
 (slack p (projectedOutcome group outcome)+weightSum difference (update group outcome)-weightSum difference group)%2=0 := by
 cases outcome with
 |walk target=>simp only [projectedOutcome,slack,update,Int.zero_add,Int.sub_self];decide
 |push source ending=>
  by_cases owner : source∈group
  ·have sourceCrate := active_crates valid (head_nonempty head) (inside owner)
   have erased := weightSum_erase difference group source owner
   cases ending with
   |stay dest=>
    have target := (stay_geometry head effect).2
    have different := ConsumedParity11.stay_distinct head effect tail completed
    have nextValid := HazardPhases.step_good NetHack.SokobanLinearPhases.Map12.certificate state dir t valid head
    have holesEq : t.state.holes=state.holes := by rw [effect.2]
    have nextNonempty : t.state.holes≠[] := by rw [holesEq];exact head_nonempty head
    have present : dest∈t.state.boulders := by rw [effect.2];simp
    have destCrate := active_crates nextValid nextNonempty present
    have numeric := (row source dest dir sourceCrate target different).1 destCrate
    have same : slack p (projectedOutcome group (.push source (.stay dest)))+
        weightSum difference (update group (.push source (.stay dest)))-weightSum difference group=
        1+q dest-q source := by
      simp only [projectedOutcome,if_pos owner,slack,update,move,post,weightSum]
      unfold difference at erased ⊢
      omega
    rw [same]
    exact numeric
   |fill hole=>
    have target := fill_geometry head effect
    have different : hole≠source := by
      intro same
      obtain ⟨phase,bound,holes,hero,boxes⟩ := valid.2
      have sourceNotHole : source∉state.holes := by
        have checked : crates.all (fun c=>decide (c∉soko1_2.initial.holes))=true := by decide +kernel
        have absent := of_decide_eq_true (List.all_eq_true.mp checked source sourceCrate)
        exact fun member=>absent ((List.drop_sublist phase soko1_2.initial.holes).subset (holes ▸ member))
      exact sourceNotHole (same ▸ effect.2.1)
    obtain ⟨phase,atIndex⟩ := valid.2
    have holesInside : state.holes⊆soko1_2.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase _).subset
    have numeric := (row source hole dir sourceCrate target different).2 (holesInside effect.2.1)
    have same : slack p (projectedOutcome group (.push source (.fill hole)))+
        weightSum difference (update group (.push source (.fill hole)))-weightSum difference group=
        1-p.hole hole-q source := by
      simp only [projectedOutcome,if_pos owner,slack,update,move,post]
      change weightSum difference group=(q source-p.boulder source)+weightSum difference (group.erase source) at erased
      omega
    rw [same]
    exact numeric
  ·cases ending <;> simp only [projectedOutcome,if_neg owner,slack,update,move,Int.zero_add,Int.sub_self] <;> decide

theorem aux_even {state dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes) (completed : Goal final)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map12.certificate state)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) :
 (ownSlack p group outcomes+weightSum difference (endGroup group outcomes)-weightSum difference group)%2=0 := by
 induction logged generalizing group with
 |nil=>simp only [ownSlack,endGroup,Int.zero_add,Int.sub_self];decide
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
  have nextValid := HazardPhases.step_good NetHack.SokobanLinearPhases.Map12.certificate state dir t valid head
  have actual := step_boulders_nodup _ _ _ _ valid.1 head
  have nextUnique := GhostSubset.update_unique _ _ _ effect actual group unique inside
  have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
  have nextEven := ih completed nextValid (update group outcome) nextUnique nextInside
  have stepEven := one_even valid head effect tail completed group inside
  change ((slack p (projectedOutcome group outcome)+ownSlack p (update group outcome) outcomes)+
    weightSum difference (endGroup (update group outcome) outcomes)-weightSum difference group)%2=0
  omega

theorem compatible_sum (group : List Cell) (compatible : ∀c∈group,difference c%2=0) :
 (weightSum difference group)%2=0 := by
 induction group with
 |nil=>decide
 |cons c rest ih=>
  have one := compatible c (by simp)
  have tail := ih (fun c member=>compatible c (List.mem_cons_of_mem _ member))
  change (difference c+weightSum difference rest)%2=0
  omega

/-- Every absorbed compatible selected group has even raw owned energy.
The start is any actually reached state; all rolling fills are included. -/
theorem consumed_even {state dirs final pushes moves outcomes history past pastMoves}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders)
 (gone : endGroup group outcomes=[]) (compatible : ∀c∈group,difference c%2=0) :
 (energy p group outcomes)%2=0 := by
 have aux := aux_even logged completed (NetHack.SokobanLinearPhases.Map12.trace_phase_invariant reached) group unique inside
 have start := compatible_sum group compatible
 rw [gone] at aux
 simp only [weightSum] at aux
 change (ownSlack p group outcomes+debtOf p (endGroup group outcomes))%2=0
 rw [gone]
 simp only [debtOf,weightSum,Int.add_zero]
 omega

theorem left_compatible (group : List Cell) (inside : group⊆Left) : ∀c∈group,difference c%2=0 := by
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp initial_left_checked c (inside member))
#print axioms aux_even
#print axioms consumed_even
#print axioms left_compatible
end Owner1007.ConsumedParity12
