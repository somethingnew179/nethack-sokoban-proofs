import Owner1007.CageLedger12
import Owner1007.VerticalPair12
import Owner1007.RingAfter12
import Owner1007.NorthBound12
namespace Owner1007.TwoReserves12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem add_le_energy {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential)
    (actualUnique : initial.boulders.Nodup)
    (a b group : List Cell) (abUnique : (a++b).Nodup) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (inside : a++b ⊆ group) :
    energy potential a outcomes + energy potential b outcomes ≤ energy potential group outcomes := by
  have smallActual := List.Subset.trans inside subset
  have split := logged.energy_split actualUnique potential a b abUnique smallActual
  have mono := logged.energy_mono valid actualUnique (a++b) group abUnique unique smallActual subset inside
  omega

def ring (far : Bool) : List Cell := if far then RingAfter12.locks true 0 else RingCut12.locks 0
def region (far : Bool) : List Cell := if far then RingAfter12.region true 0 else RingCut12.region 0
theorem ring_unique : ∀ far, (ring far).Nodup := by decide +kernel

theorem ring_two (far : Bool) {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    (hero : state.player ∈ region far) (inside : ring far ⊆ group) :
    2 ≤ energy p group outcomes := by
  cases far with
  | true =>
    exact RingAfter12.owned_energy_two true logged reached group unique subset completed hero inside
  | false =>
    change state.player ∈ RingCut12.region 0 at hero
    change RingCut12.locks 0 ⊆ group at inside
    have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingCut12.matrix
    exact closedExcept_energy closed RingCut12.unique (by decide +kernel) 2 NorthBound12.ring_priced
      logged reached group unique subset completed hero inside

theorem upper_ring_four (far : Bool) {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    (hero : state.player ∈ region far)
    (bonus : RightEnergy12.cert.bonus state.player
      (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2)
    (upperInside : CageLedger12.Upper ⊆ group) (ringInside : ring far ⊆ group) :
    4 ≤ energy p group outcomes := by
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  have uActual := List.Subset.trans upperInside subset
  have rActual := List.Subset.trans ringInside subset
  have up := RightEnergy12.raw_group_energy logged reached CageLedger12.Upper
    (by decide +kernel) uActual completed
  rw [bonus] at up
  change 2 ≤ energy p CageLedger12.Upper outcomes at up
  have ri := ring_two far logged reached (ring far) (ring_unique far) rActual completed hero (fun _ h=>h)
  have abUnique : (CageLedger12.Upper++ring far).Nodup := by cases far <;> decide +kernel
  have both : CageLedger12.Upper++ring far ⊆ group :=
    List.append_subset.mpr ⟨upperInside,ringInside⟩
  have sum := add_le_energy logged Generated.soko1_2_potential_valid actualUnique
    CageLedger12.Upper (ring far) group abUnique unique subset both
  change energy p CageLedger12.Upper outcomes + energy p (ring far) outcomes ≤ energy p group outcomes at sum
  omega

theorem pair_ring_four (upper far : Bool) {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    (heroRing : state.player ∈ region far)
    (heroPair : state.player ∈ VerticalPair12.region upper 0)
    (pairInside : VerticalPair12.pair upper ⊆ group) (ringInside : ring far ⊆ group) :
    4 ≤ energy p group outcomes := by
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  have aActual := List.Subset.trans pairInside subset
  have rActual := List.Subset.trans ringInside subset
  have aUnique : (VerticalPair12.pair upper).Nodup := by cases upper <;> decide +kernel
  have a := VerticalPair12.owned_energy_two upper logged reached (VerticalPair12.pair upper)
    aUnique aActual heroPair (fun _ h=>h)
  have b := ring_two far logged reached (ring far) (ring_unique far) rActual completed heroRing (fun _ h=>h)
  have abUnique : (VerticalPair12.pair upper++ring far).Nodup := by cases upper <;> cases far <;> decide +kernel
  have both : VerticalPair12.pair upper++ring far ⊆ group :=
    List.append_subset.mpr ⟨pairInside,ringInside⟩
  have sum := add_le_energy logged Generated.soko1_2_potential_valid actualUnique
    (VerticalPair12.pair upper) (ring far) group abUnique unique subset both
  change 2 ≤ energy p (VerticalPair12.pair upper) outcomes at a
  change energy p (VerticalPair12.pair upper) outcomes + energy p (ring far) outcomes ≤ energy p group outcomes at sum
  omega
#print axioms upper_ring_four
#print axioms pair_ring_four
end Owner1007.TwoReserves12
