import Owner1007.OwnedEventsMore12
import Owner1007.LockedTokens
namespace Owner1007.RingAfter12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks (far : Bool) (_ : Fin 1) : List Cell :=
  if far then [210,237,263,289] else [236,237,263,290]
def pocket (far : Bool) : List Cell :=
  if far then [236,262,288] else [262,288,289]
def region (far : Bool) (_ : Fin 1) : List Cell :=
  soko1_2.board.floor.filter fun c => !(pocket far).contains c && !(locks far 0).contains c
def paid (far : Bool) (source : Cell) (dir : Dir) : Prop :=
  if far then
    (source=210 ∧ dir=.south) ∨ (source=237 ∧ dir=.west) ∨
    (source=263 ∧ dir=.west) ∨ (source=289 ∧ dir=.west)
  else
    (source=236 ∧ dir=.south) ∨ (source=263 ∧ dir=.west) ∨ (source=290 ∧ dir=.west)
instance (far : Bool) (source : Cell) (dir : Dir) : Decidable (paid far source dir) := by
  unfold paid
  infer_instance
theorem matrix : ∀ far : Bool,
    PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes (locks far) (region far) (paid far) = true := by
  decide +kernel
theorem unique : ∀ far i, (locks far i).Nodup := by decide +kernel
theorem large : ∀ far i, 2 < (locks far i).length := by decide +kernel
theorem paid_cost : ∀ far : Bool, ∀ source ∈ locks far 0, ∀ dir ∈ allDirs,
    paid far source dir → ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧ (2 : Int) ≤ 1 + p.boulder dest - p.boulder source := by
  decide +kernel
theorem priced (far : Bool) : ∀ source dir, paid far source dir →
    ∀ dest ∈ pushTargets soko1_2.board source dir,
      dest ∉ soko1_2.initial.holes ∧ (2 : Int) ≤ 1 + p.boulder dest - p.boulder source := by
  intro source dir isPaid dest member
  have sourceInside : source ∈ locks far 0 := by
    cases far <;> simp only [paid,Bool.false_eq_true,Bool.true_eq,if_false,if_true] at isPaid <;>
      rcases isPaid with h | h | h | h <;> simp_all [locks]
  exact paid_cost far source sourceInside dir (Geometry.all_directions dir) isPaid dest member
theorem locked_pair : Locked soko1_2.board [210,236] :=
  locked_of_check _ _ (by decide +kernel)
theorem owned_energy_two (far : Bool)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    (hero : state.player ∈ region far 0) (inside : locks far 0 ⊆ group) :
    2 ≤ energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (matrix far)
  exact closedExcept_energy closed (unique far) (large far) 2 (priced far)
    logged reached group groupUnique subset completed hero inside
#print axioms matrix
#print axioms owned_energy_two
#print axioms locked_pair
end Owner1007.RingAfter12
