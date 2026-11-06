/- Transfer from persistent boulder groups to the ORIGINAL Model Trace.
Every original successful step is covered, and its single push/consumption
charge is assigned exactly once. Concrete PDB rows are proof obligations,
not axioms or assumptions about a searcher. No numerical minimum is claimed. -/
import NetHack.Sokoban.GhostPartition

namespace NetHack.Sokoban.GhostPartition
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open HazardPattern LowerBounds

theorem group_subset (state : State) (groups : List (List Cell))
    (coupled : Coupled state groups) (group : List Cell) (member : group ∈ groups) :
    group ⊆ state.boulders := by
  intro cell present
  exact coupled.mem_iff.mp (List.mem_flatten.mpr ⟨group,member,present⟩)

theorem group_unique (groups : List (List Cell)) (unique : groups.flatten.Nodup)
    (group : List Cell) (member : group ∈ groups) : group.Nodup := by
  induction groups with
  | nil => simp at member
  | cons first rest ih =>
    have pieces := List.nodup_append.mp unique
    rcases List.mem_cons.mp member with rfl|later
    · exact pieces.1
    · exact ih pieces.2.1 later

theorem sum_bounds (groups : List (List Cell)) (before cost after : List Cell → Int)
    (rows : ∀ group ∈ groups, before group ≤ cost group + after group) :
    sumGroups before groups ≤ sumGroups cost groups + sumGroups after groups := by
  induction groups with
  | nil => exact Int.le_refl _
  | cons first rest ih =>
    have a := rows first List.mem_cons_self
    have b := ih (fun g member => rows g (List.mem_cons_of_mem _ member))
    simp only [sumGroups]
    omega

theorem sum_update (groups : List (List Cell)) (f : List Cell → Int) (outcome : Outcome) :
    sumGroups (fun g => f (update g outcome)) groups =
      sumGroups f (groups.map (fun g => update g outcome)) := by
  induction groups with
  | nil => rfl
  | cons first rest ih => simp only [sumGroups,List.map_cons,ih]

theorem sum_zero (groups : List (List Cell)) : sumGroups (fun _ => (0 : Int)) groups = 0 := by
  induction groups with
  | nil => rfl
  | cons first rest ih => simp only [sumGroups,ih,Int.zero_add]

theorem sum_nonpositive (groups : List (List Cell)) (f : List Cell → Int)
    (rows : ∀ group ∈ groups, f group ≤ 0) : sumGroups f groups ≤ 0 := by
  induction groups with
  | nil => exact Int.le_refl _
  | cons first rest ih =>
    have a := rows first List.mem_cons_self
    have b := ih (fun g member => rows g (List.mem_cons_of_mem _ member))
    simp only [sumGroups]; omega

structure GroupCertificate (board : Board) (limit : Nat) (invariant : State → Prop) where
  groupValue : State → List Cell → Int
  holeWeight : Cell → Int
  unique : ∀ s, invariant s → s.boulders.Nodup
  preserved : ∀ s d t, invariant s → step board s d = some t → invariant t.state
  row : ∀ s d t outcome group, invariant s →
    group.Nodup → group ⊆ s.boulders → group.length ≤ limit →
    step board s d = some t → Matches s t outcome →
    groupValue s group ≤ charge holeWeight group outcome + groupValue t.state (update group outcome)
  terminal : ∀ s group, invariant s → Goal s → group.Nodup →
    group ⊆ s.boulders → group.length ≤ limit → groupValue s group ≤ 0

def partitionValue (cert : GroupCertificate board limit invariant)
    (state : State) (groups : List (List Cell)) : Int :=
  sumGroups (cert.groupValue state) groups + weightSum cert.holeWeight state.holes

theorem partition_step_bound (cert : GroupCertificate board limit invariant)
    (state : State) (groups : List (List Cell)) (direction : Dir) (t : Transition)
    (good : invariant state) (coupled : Coupled state groups) (bounded : Capacity limit groups)
    (checked : step board state direction = some t) (outcome : Outcome)
    (effect : Matches state t outcome) :
    partitionValue cert state groups ≤ Int.ofNat t.pushCost +
      partitionValue cert t.state (groups.map (fun g => update g outcome)) := by
  have unique := cert.unique state good
  have flatUnique := coupled.nodup_iff.mpr unique
  have total := sum_bounds groups (cert.groupValue state)
    (fun g => charge cert.holeWeight g outcome)
    (fun g => cert.groupValue t.state (update g outcome)) (fun group member =>
      cert.row state direction t outcome group good (group_unique groups flatUnique group member)
        (group_subset state groups coupled group member) (bounded group member) checked effect)
  rw [sum_update] at total
  cases outcome with
  | walk target =>
    have costs : sumGroups (fun g => charge cert.holeWeight g (.walk target)) groups = 0 :=
      sum_zero groups
    rw [costs] at total
    change t = {state := {state with player := target}, pushed := false, filled := none} at effect
    subst t
    simpa [partitionValue,update,Transition.pushCost] using total
  | push source result =>
    have present : source ∈ state.boulders := by cases result <;> exact effect.1
    have selected : source ∈ groups.flatten := coupled.mem_iff.mpr present
    cases result with
    | stay landing =>
      have costs : sumGroups (fun g => charge cert.holeWeight g (.push source (.stay landing))) groups = 1 :=
        sum_owner groups source 1 flatUnique selected
      rw [costs] at total
      unfold partitionValue
      rw [effect.2]
      simp only [Transition.pushCost,↓reduceIte,Int.ofNat_eq_natCast]
      simp only [effect.2] at total
      omega
    | fill hole =>
      have costs : sumGroups (fun g => charge cert.holeWeight g (.push source (.fill hole))) groups =
          1 - cert.holeWeight hole :=
        sum_owner groups source (1-cert.holeWeight hole) flatUnique selected
      have oldHoles := weightSum_erase cert.holeWeight state.holes hole effect.2.1
      rw [costs] at total
      unfold partitionValue
      rw [effect.2.2]
      simp only [Transition.pushCost,↓reduceIte,Int.ofNat_eq_natCast]
      simp only [effect.2.2] at total
      omega

/-- For every original Trace, bookkeeping groups can be transported to its
real final state, with no loss of boulders at a pattern-window boundary. -/
theorem partition_trace_bound (cert : GroupCertificate board limit invariant)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (groups : List (List Cell)) (good : invariant initial)
    (coupled : Coupled initial groups) (bounded : Capacity limit groups) :
    ∃ finalGroups, Coupled final finalGroups ∧ Capacity limit finalGroups ∧
      partitionValue cert initial groups ≤ Int.ofNat pushes + partitionValue cert final finalGroups := by
  induction trace generalizing groups with
  | nil => exact ⟨groups,coupled,bounded,by simp⟩
  | cons head tail ih =>
    rcases stepOracle_covers board _ (cert.unique _ good) _ _ head with ⟨outcome,_,effect⟩
    have nextCoupled := update_coupled _ groups _ (cert.unique _ good) coupled outcome effect
    have nextBounded := update_capacity limit groups outcome bounded
    rcases ih (groups.map (fun g => update g outcome)) (cert.preserved _ _ _ good head)
      nextCoupled nextBounded with ⟨finalGroups,lastCoupled,lastBounded,rest⟩
    have first := partition_step_bound cert _ groups _ _ good coupled bounded head outcome effect
    refine ⟨finalGroups,lastCoupled,lastBounded,?_⟩
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at first rest ⊢
    omega

theorem partition_goal_bound (cert : GroupCertificate board limit invariant)
    (state : State) (groups : List (List Cell)) (good : invariant state)
    (coupled : Coupled state groups) (bounded : Capacity limit groups) (completed : Goal state) :
    partitionValue cert state groups ≤ 0 := by
  have flatUnique := coupled.nodup_iff.mpr (cert.unique _ good)
  have rows : ∀ group ∈ groups, cert.groupValue state group ≤ 0 := by
    intro group member
    exact cert.terminal state group good completed (group_unique groups flatUnique group member)
      (group_subset state groups coupled group member) (bounded group member)
  have sum := sum_nonpositive groups (cert.groupValue state) rows
  have empty : state.holes = [] := completed
  simpa only [partitionValue,empty,weightSum,Int.add_zero] using sum

theorem partition_invariant_final (cert : GroupCertificate board limit invariant)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (good : invariant initial) : invariant final := by
  induction trace with
  | nil => exact good
  | cons head tail ih => exact ih (cert.preserved _ _ _ good head)

/-- A completed concrete group certificate would give a universal original
push lower bound. Numerical solver output alone cannot instantiate cert.row. -/
theorem partition_pushes_lower_bound (cert : GroupCertificate board limit invariant)
    (initial : State) (groups : List (List Cell)) (good : invariant initial)
    (coupled : Coupled initial groups) (bounded : Capacity limit groups)
    (cost : Nat) (initialValue : partitionValue cert initial groups = Int.ofNat cost)
    {final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) : cost ≤ pushes := by
  rcases partition_trace_bound cert trace groups good coupled bounded with ⟨finalGroups,a,b,total⟩
  have finalGood := partition_invariant_final cert trace good
  have terminal := partition_goal_bound cert final finalGroups finalGood a b completed
  rw [initialValue] at total
  simp only [Int.ofNat_eq_natCast] at total
  omega

end NetHack.Sokoban.GhostPartition
