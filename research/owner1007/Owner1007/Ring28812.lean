import Owner1007.RingAfter12
namespace Owner1007.Ring28812
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks (_ : Fin 1) : List Cell := [210,237,263,288]
def pocket : List Cell := [236,262]
def region (_ : Fin 1) : List Cell :=
 soko1_2.board.floor.filter fun c => !pocket.contains c && !(locks 0).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210 ∧ dir=.south) ∨ (source=237 ∧ dir=.west) ∨ (source=263 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem large : ∀ i, 2<(locks i).length := by decide +kernel
theorem priced : ∀ source dir, paid source dir → ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧ (2:Int)≤1+p.boulder dest-p.boulder source := by
 intro source dir isPaid
 rcases isPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel
theorem owned_energy_two
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (uniqueG : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player∈region 0) (inside : locks 0⊆group) :
 2≤energy p group outcomes := by
 exact closedExcept_energy (PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix) unique large 2 priced
  logged reached group uniqueG subset completed hero inside
#print axioms owned_energy_two
end Owner1007.Ring28812
