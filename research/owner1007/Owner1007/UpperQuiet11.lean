import Owner1007.OneWayToken11
import Owner1007.UpperNoReturn11
import Owner1007.OwnedCorral11
namespace Owner1007.UpperQuiet11
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting

inductive Quiet (paid : Cell → Dir → Prop) :
    State → List Cell → List Dir → State → Nat → Nat → List Outcome → Prop where
  | nil (state group) : Quiet paid state group [] state 0 0 []
  | cons {state group dir t rest final pushes moves outcome outcomes}
      (checked : step soko1_1.board state dir = some t) (effect : Matches state t outcome)
      (avoid : ¬ OwnedCorral11.PaidStep paid group dir t)
      (tail : Quiet paid t.state (update group outcome) rest final pushes moves outcomes) :
      Quiet paid state group (dir :: rest) final (t.pushCost+pushes) (1+moves) (outcome::outcomes)

theorem Quiet.logged {paid initial group dirs final pushes moves outcomes}
    (quiet : Quiet paid initial group dirs final pushes moves outcomes) :
    Logged soko1_1.board initial dirs final pushes moves outcomes := by
  induction quiet with
  | nil => exact .nil _
  | cons checked effect avoid tail ih => exact .cons checked effect ih

theorem lock_complete (i : Fin 19) (group : List Cell)
    (bounded : group.length ≤ 3) (inside : UpperZero11.locks i ⊆ group)
    (source : Cell) (owner : source ∈ group) : source ∈ UpperZero11.locks i := by
  by_cases member : source ∈ UpperZero11.locks i
  · exact member
  · have all : source :: UpperZero11.locks i ⊆ group := by
      intro c found
      rcases List.mem_cons.mp found with rfl | later
      · exact owner
      · exact inside later
    have card := List.Nodup.length_le_of_subset
      (List.nodup_cons.mpr ⟨member,UpperZero11.unique i⟩) all
    simp only [List.length_cons,UpperZero11.size i] at card
    omega

theorem stay_geometry {state : State} {dir : Dir} {t : Transition} {source landing : Cell}
    (checked : step soko1_1.board state dir = some t)
    (effect : Matches state t (.push source (.stay landing))) :
    dir.diagonal=false ∧ landing ∈ pushTargets soko1_1.board source dir := by
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

theorem step_no_return {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
    (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
    (bounded : group.length ≤ 3) (checked : step soko1_1.board state dir = some t)
    (effect : Matches state t outcome) (avoid : ¬ OwnedCorral11.PaidStep UpperZero11.paid group dir t)
    (cell : Cell) (initial : cell ∈ [137,139,191]) :
    OneWayToken11.AvoidLanding cell group outcome := by
  cases outcome with
  | walk _ => trivial
  | push source result =>
    cases result with
    | fill _ => trivial
    | stay landing =>
      intro owner
      obtain ⟨i,heroInside,inside⟩ := good
      have member := lock_complete i group bounded inside source owner
      have unpaid : ¬ UpperZero11.paid source dir := by
        intro paid
        exact avoid ⟨source,owner,by rw [effect.2],paid⟩
      obtain ⟨cardinal,target⟩ := stay_geometry checked effect
      have away := UpperNoReturn11.landing_avoids i source landing dir member cardinal unpaid target
      simp at initial
      rcases initial with rfl | rfl | rfl <;> first | exact away.1 | exact away.2.1 | exact away.2.2

theorem Quiet.no_return
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region UpperZero11.paid)
    {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (quiet : Quiet UpperZero11.paid state group dirs final pushes moves outcomes)
    (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (bounded : group.length ≤ 3) (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
    (holesInside : state.holes ⊆ soko1_1.initial.holes) (cell : Cell) (initial : cell ∈ [137,139,191]) :
    OneWayToken11.NoReturn cell group outcomes := by
  induction quiet with
  | nil => trivial
  | @cons state group dir t rest final pushes moves outcome outcomes checked effect avoid tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique inside
    have nextInside := GhostSubset.update_subset state t outcome effect group unique inside
    have nextBound := Nat.le_trans (update_length group outcome) bounded
    have nextGood := OwnedCorral11.step_good_except closed UpperZero11.unique UpperZero11.size
      good inside bounded holesInside checked effect avoid
    have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ checked).subset holesInside
    exact ⟨step_no_return good bounded checked effect avoid cell initial,
      ih nextActual nextUnique nextInside nextBound nextGood nextHoles⟩

theorem Quiet.stationary
    (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes UpperZero11.locks UpperZero11.region UpperZero11.paid)
    {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (quiet : Quiet UpperZero11.paid state group dirs final pushes moves outcomes)
    (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (bounded : group.length ≤ 3) (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
    (holesInside : state.holes ⊆ soko1_1.initial.holes) (cell : Cell) (initial : cell ∈ [137,139,191])
    (present : cell ∈ endGroup group outcomes) : ownPushes [cell] outcomes=0 :=
  (OneWayToken11.historical quiet.logged actualUnique cell group unique inside
    (quiet.no_return closed actualUnique unique inside bounded good holesInside cell initial) present).2

#print axioms Quiet.stationary
end Owner1007.UpperQuiet11
