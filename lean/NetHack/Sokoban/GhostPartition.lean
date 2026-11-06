/- Persistent groups of ACTUAL boulders for additive puzzle certificates.
Groups are proof bookkeeping, never extra Model state or a Trace premise.
A boulder leaves its group only when Model consumes it; leaving a spatial
window does not erase its identity. The moved group alone pays the push.
No PDB, solver, hero-region quotient or numerical bound is trusted here. -/
import NetHack.Sokoban.HazardPhases

namespace NetHack.Sokoban.GhostPartition
open HazardPattern LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def post (boxes : List Cell) (source : Cell) : Ending → List Cell
  | .stay landing => landing :: boxes.erase source
  | .fill _ => boxes.erase source

def move (group : List Cell) (source : Cell) (result : Ending) : List Cell :=
  if source ∈ group then post group source result else group

def update (group : List Cell) : Outcome → List Cell
  | .walk _ => group
  | .push source result => move group source result

def Coupled (state : State) (groups : List (List Cell)) : Prop :=
  groups.flatten.Perm state.boulders

def Capacity (limit : Nat) (groups : List (List Cell)) : Prop :=
  ∀ group ∈ groups, group.length ≤ limit

theorem move_absent (groups : List (List Cell)) (source : Cell) (result : Ending)
    (absent : source ∉ groups.flatten) : groups.map (fun g => move g source result) = groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    have a : source ∉ group := fun h => absent (List.mem_append_left _ h)
    have b : source ∉ rest.flatten := fun h => absent (List.mem_append_right _ h)
    rw [List.map_cons,ih b]
    simp only [move,if_neg a]

/-- The groups retain exactly the real post-push multiset, including the
consumption of a single boulder at the first open PIT/HOLE. -/
theorem move_flatten (groups : List (List Cell)) (source : Cell) (result : Ending)
    (unique : groups.flatten.Nodup) (present : source ∈ groups.flatten) :
    (groups.map (fun g => move g source result)).flatten.Perm
      (post groups.flatten source result) := by
  induction groups with
  | nil => simp at present
  | cons group rest ih =>
    have pieces := List.nodup_append.mp unique
    by_cases member : source ∈ group
    · have absent : source ∉ rest.flatten := by
        intro h
        exact pieces.2.2 source member source h rfl
      rw [List.map_cons,List.flatten_cons,move,if_pos member,move_absent rest source result absent]
      cases result <;> simp only [post,List.flatten_cons,List.erase_append_left _ member,
        List.cons_append] <;> exact List.Perm.refl _
    · have later : source ∈ rest.flatten := (List.mem_append.mp present).resolve_left member
      have next := ih pieces.2.1 later
      rw [List.map_cons,List.flatten_cons,move,if_neg member]
      cases result with
      | stay landing =>
        change (group ++ (rest.map (fun g => move g source (.stay landing))).flatten).Perm
          (landing :: (group ++ rest.flatten).erase source)
        rw [List.erase_append_right _ member]
        exact (next.append_left group).trans List.perm_middle
      | fill hole =>
        change (group ++ (rest.map (fun g => move g source (.fill hole))).flatten).Perm
          ((group ++ rest.flatten).erase source)
        rw [List.erase_append_right _ member]
        exact next.append_left group

theorem update_length (group : List Cell) (outcome : Outcome) :
    (update group outcome).length ≤ group.length := by
  cases outcome with
  | walk _ => exact Nat.le_refl _
  | push source result =>
    by_cases member : source ∈ group
    · have shorter := List.length_erase_of_mem member
      have positive := List.length_pos_of_mem member
      cases result with
      | stay landing =>
        change (move group source (.stay landing)).length ≤ group.length
        rw [move,if_pos member]
        change (group.erase source).length + 1 ≤ group.length
        omega
      | fill hole =>
        change (move group source (.fill hole)).length ≤ group.length
        rw [move,if_pos member]
        change (group.erase source).length ≤ group.length
        omega
    · simp only [update,move,if_neg member]
      exact Nat.le_refl _

theorem update_capacity (limit : Nat) (groups : List (List Cell)) (outcome : Outcome)
    (bounded : Capacity limit groups) : Capacity limit (groups.map (fun g => update g outcome)) := by
  intro group member
  rcases List.mem_map.mp member with ⟨before,old,rfl⟩
  exact Nat.le_trans (update_length before outcome) (bounded before old)

theorem update_coupled (state : State) (groups : List (List Cell)) (t : Transition)
    (unique : state.boulders.Nodup) (coupled : Coupled state groups)
    (outcome : Outcome) (effect : Matches state t outcome) :
    Coupled t.state (groups.map (fun g => update g outcome)) := by
  have flatUnique := coupled.nodup_iff.mpr unique
  cases outcome with
  | walk target =>
    change t = {state := {state with player := target}, pushed := false, filled := none} at effect
    subst t
    simpa [update,Coupled] using coupled
  | push source result =>
    have present : source ∈ state.boulders := by cases result <;> exact effect.1
    have selected : source ∈ groups.flatten := coupled.mem_iff.mpr present
    have projected := move_flatten groups source result flatUnique selected
    have erased := List.Perm.erase source coupled
    cases result with
    | stay landing =>
      change ((groups.map (fun g => move g source (.stay landing))).flatten).Perm t.state.boulders
      rw [effect.2]
      exact projected.trans (erased.cons landing)
    | fill hole =>
      change ((groups.map (fun g => move g source (.fill hole))).flatten).Perm t.state.boulders
      rw [effect.2.2]
      exact projected.trans erased

def sumGroups (f : List Cell → Int) : List (List Cell) → Int
  | [] => 0
  | group :: rest => f group + sumGroups f rest

theorem one_owner (groups : List (List Cell)) (source : Cell)
    (unique : groups.flatten.Nodup) :
    sumGroups (fun group => if source ∈ group then (1 : Int) else 0) groups =
      (if source ∈ groups.flatten then 1 else 0) := by
  induction groups with
  | nil => simp [sumGroups]
  | cons group rest ih =>
    have pieces := List.nodup_append.mp unique
    have next := ih pieces.2.1
    by_cases member : source ∈ group
    · have absent : source ∉ rest.flatten := by
        intro h
        exact pieces.2.2 source member source h rfl
      simp only [sumGroups,if_pos member,next,if_neg absent,Int.add_zero]
      simp [List.mem_append,member]
    · simp only [sumGroups,if_neg member,next,Int.zero_add]
      simp [List.mem_append,member]

def charge (holeWeight : Cell → Int) (group : List Cell) : Outcome → Int
  | .walk _ => 0
  | .push source (.stay _) => if source ∈ group then 1 else 0
  | .push source (.fill hole) => if source ∈ group then 1 - holeWeight hole else 0

theorem sum_absent (groups : List (List Cell)) (source : Cell) (cost : Int)
    (absent : source ∉ groups.flatten) :
    sumGroups (fun group => if source ∈ group then cost else 0) groups = 0 := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    have a : source ∉ group := fun h => absent (List.mem_append_left _ h)
    have b : source ∉ rest.flatten := fun h => absent (List.mem_append_right _ h)
    simp only [sumGroups,if_neg a,ih b,Int.zero_add]

theorem sum_owner (groups : List (List Cell)) (source : Cell) (cost : Int)
    (unique : groups.flatten.Nodup) (present : source ∈ groups.flatten) :
    sumGroups (fun group => if source ∈ group then cost else 0) groups = cost := by
  induction groups with
  | nil => simp at present
  | cons group rest ih =>
    have pieces := List.nodup_append.mp unique
    by_cases member : source ∈ group
    · have absent : source ∉ rest.flatten := by
        intro h
        exact pieces.2.2 source member source h rfl
      have zero := sum_absent rest source cost absent
      simp only [sumGroups,if_pos member,zero,Int.add_zero]
    · have later : source ∈ rest.flatten := (List.mem_append.mp present).resolve_left member
      simp only [sumGroups,if_neg member,ih pieces.2.1 later,Int.zero_add]

end NetHack.Sokoban.GhostPartition
