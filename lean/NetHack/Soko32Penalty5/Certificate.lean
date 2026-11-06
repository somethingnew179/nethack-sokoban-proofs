/- Sparse certificates for the explicitly weighted relaxation. All row,
walk, action and terminal obligations are transparent finite computations.
Missing/zero rows have zero credit; a searcher's closure claim is not used. -/
import NetHack.Soko32Penalty5.Graph
import NetHack.Sokoban.NonlinearFacts
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.IndexedCertificateTable

structure Row where
  boxes : List Cell
  reach : Nat
  value : Nat
  links : List (Nat × Nat)
  deriving Repr

def zeroRow : Row := ⟨[],0,0,[]⟩
def link : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (a,b)::rest, i => if i = a then b else link rest i
def debt (boxes : List Cell) : Int :=
  weightSum (fun c => -Generated.soko3_2Potential.boulder c) boxes

def walkCheck (heroes : List Cell) (r : Row) : Bool := heroes.all fun hero =>
  if r.reach.testBit hero then allDirs.all fun dir =>
    match walking r.boxes hero dir with
    | none => true
    | some target => heroes.contains target && r.reach.testBit target
  else true

def pushCheck (actions : List Action) (table : Table Row) (r : Row) : Bool :=
  actions.zipIdx.all fun (a,i) =>
    if r.reach.testBit a.hero && decide (a.enabled r.boxes a.hero) && decide (a.cost < r.value) then
      let after := get zeroRow table (link r.links i)
      decide ((a.after r.boxes).Perm after.boxes) && after.reach.testBit a.source &&
        decide (r.value ≤ a.cost + after.value)
    else true

def check (heroes : List Cell) (actions : List Action) (table : Table Row) (_ : Nat) (r : Row) : Bool :=
  if r.value = 0 then true else
    walkCheck heroes r && pushCheck actions table r &&
      decide (r.boxes.length ≤ 4 → Int.ofNat r.value ≤ debt r.boxes)

structure Sound (heroes : List Cell) (actions : List Action) (table : Table Row) (r : Row) : Prop where
  walk : r.value ≠ 0 → ∀ hero ∈ heroes, r.reach.testBit hero = true → ∀ dir target,
    walking r.boxes hero dir = some target → target ∈ heroes ∧ r.reach.testBit target = true
  push : r.value ≠ 0 → ∀ a ∈ actions, r.reach.testBit a.hero = true →
    a.enabled r.boxes a.hero → a.cost < r.value →
    ∃ i, (a.after r.boxes).Perm (get zeroRow table i).boxes ∧
      (get zeroRow table i).reach.testBit a.source = true ∧ r.value ≤ a.cost + (get zeroRow table i).value
  terminal : r.boxes.length ≤ 4 → Int.ofNat r.value ≤ debt r.boxes

theorem debt_nonnegative (boxes : List Cell) : 0 ≤ debt boxes :=
  NonlinearFacts.weightSum_nonnegative _ boxes (fun c => by
    have := Generated.soko3_2_potential_valid.nonpositive c; omega)

theorem check_sound (heroes : List Cell) (actions : List Action) (table : Table Row) (i : Nat) (r : Row)
    (checked : check heroes actions table i r = true) : Sound heroes actions table r := by
  by_cases zero : r.value = 0
  · exact ⟨fun h => (h zero).elim,fun h => (h zero).elim,fun _ => by
      rw [zero]; exact debt_nonnegative r.boxes⟩
  simp only [check,if_neg zero,Bool.and_eq_true_iff] at checked
  refine ⟨?_,?_,of_decide_eq_true checked.2⟩
  · intro _ hero member present dir target edge
    have row := List.all_eq_true.mp checked.1.1 hero member
    simp only [present,↓reduceIte] at row
    have hit := List.all_eq_true.mp row dir (Geometry.all_directions dir)
    simp only [edge,Bool.and_eq_true_iff,List.contains_iff_mem] at hit
    exact hit
  · intro _ a member present enabled cheaper
    have mapped : a ∈ actions.zipIdx.map Prod.fst := by
      rw [List.zipIdx_map_fst]; exact member
    obtain ⟨⟨b,j⟩,zipped,equal⟩ := List.mem_map.mp mapped
    change b = a at equal
    subst b
    have row := List.all_eq_true.mp checked.1.2 (a,j) zipped
    simp only [present,enabled,cheaper,decide_true,Bool.true_and,↓reduceIte,
      Bool.and_eq_true_iff] at row
    exact ⟨link r.links j,of_decide_eq_true row.1.1,row.1.2,of_decide_eq_true row.2⟩

end NetHack.Soko32Penalty5
