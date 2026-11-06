/- Soundness of a complete finite weighted certificate. No solver result
occurs among the premises: all positive rows must pass the kernel checker. -/
import NetHack.Soko32Penalty5.Certificate
namespace NetHack.Soko32Penalty5
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.IndexedCertificateTable

inductive Ticket (heroes : List Cell) (table : Table Row) (boxes : List Cell) (hero : Cell) : Nat → Prop where
  | zero : Ticket heroes table boxes hero 0
  | row (index : Nat) (same : boxes.Perm (get zeroRow table index).boxes)
      (inside : hero ∈ heroes) (reached : (get zeroRow table index).reach.testBit hero = true) :
      Ticket heroes table boxes hero (get zeroRow table index).value

theorem ticket_step (heroes : List Cell) (actions : List Action) (table : Table Row)
    (checked : ∀ i, Sound heroes actions table (get zeroRow table i))
    (sources : ∀ a ∈ actions, a.source ∈ heroes)
    {boxes final : List Cell} {hero target cost value : Nat}
    (edge : Edge actions boxes hero final target cost) (ticket : Ticket heroes table boxes hero value) :
    ∃ next, Ticket heroes table final target next ∧ value ≤ cost + next := by
  cases ticket with
  | zero => exact ⟨0,.zero,by omega⟩
  | row i same inside reached =>
    by_cases enough : (get zeroRow table i).value ≤ cost
    · exact ⟨0,.zero,by omega⟩
    have positive : (get zeroRow table i).value ≠ 0 := by omega
    cases edge with
    | @walk dir target walked =>
      have small : walking (get zeroRow table i).boxes hero dir = some target :=
        (walking_perm same hero dir).symm.trans walked
      obtain ⟨member,found⟩ := (checked i).walk positive hero inside reached dir target small
      exact ⟨_,.row i same member found,by omega⟩
    | push a member legal =>
      have legalRow := (enabled_perm a same hero).mp legal
      have heroEq := legal.1
      have enabled : a.enabled (get zeroRow table i).boxes a.hero := by simpa only [heroEq] using legalRow
      have reach : (get zeroRow table i).reach.testBit a.hero = true := by simpa only [heroEq] using reached
      obtain ⟨j,after,found,bound⟩ := (checked i).push positive a member reach enabled (by omega)
      exact ⟨_,.row j ((after_perm a same).trans after) (sources a member) found,bound⟩

theorem ticket_terminal (heroes : List Cell) (actions : List Action) (table : Table Row)
    (checked : ∀ i, Sound heroes actions table (get zeroRow table i))
    {boxes : List Cell} {hero value : Nat} (ticket : Ticket heroes table boxes hero value)
    (terminal : boxes.length ≤ 4) : Int.ofNat value ≤ debt boxes := by
  cases ticket with
  | zero => exact debt_nonnegative boxes
  | row i same _ _ =>
    have bound := (checked i).terminal (by simpa only [←same.length_eq] using terminal)
    have equal := StatePermutation.weightSum_permutation
      (fun c => -Generated.soko3_2Potential.boulder c) same
    change debt boxes = debt (get zeroRow table i).boxes at equal
    omega

theorem path_bound (heroes : List Cell) (actions : List Action) (table : Table Row)
    (checked : ∀ i, Sound heroes actions table (get zeroRow table i))
    (sources : ∀ a ∈ actions, a.source ∈ heroes)
    {initial final : List Cell} {hero finish cost value : Nat}
    (path : Path actions initial hero final finish cost)
    (ticket : Ticket heroes table initial hero value) (terminal : final.length ≤ 4) :
    Int.ofNat value ≤ Int.ofNat cost + debt final := by
  induction path generalizing value with
  | nil =>
    have last := ticket_terminal heroes actions table checked ticket terminal
    change Int.ofNat value ≤ (0 : Int) + debt _
    omega
  | cons head tail ih =>
    obtain ⟨next,transport,bound⟩ := ticket_step heroes actions table checked sources head ticket
    have rest := ih transport
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at rest ⊢
    omega

end NetHack.Soko32Penalty5
