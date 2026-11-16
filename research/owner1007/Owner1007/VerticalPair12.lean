import Owner1007.RightPrice4
namespace Owner1007.VerticalPair12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def pair (upper : Bool) : List Cell := if upper then [160,186] else [186,212]
def locks (upper : Bool) (i : Fin 2) : List Cell := if i.val=0 then pair upper else []
def region (upper : Bool) (i : Fin 2) : List Cell :=
  soko1_2.board.floor.filter fun c => !(locks upper i).contains c
def credit (i : Fin 2) : Int := if i.val=0 then 2 else 0
theorem matrix : ∀ upper : Bool, PricedCorral.check soko1_2.board soko1_2.initial.holes p
    (locks upper) (region upper) credit = true := by decide +kernel
theorem unique : ∀ upper i, (locks upper i).Nodup := by decide +kernel
theorem debt_credit : ∀ upper i, credit i ≤ debtOf p (locks upper i) := by decide +kernel

/-- A vertical blocking pair costs two further owned units, either through
a push or through retained terminal debt. No completion premise is needed. -/
theorem owned_energy_two (upper : Bool)
    {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    (hero : state.player ∈ region upper 0) (inside : pair upper ⊆ group) :
    2 ≤ energy p group outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ (matrix upper)
  obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed (unique upper)
    logged reached group groupUnique subset hero inside
  have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -p.boulder c)
    (locks upper j) (endGroup group outcomes)
    (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c ≤ 0 at h; omega)
    (unique upper j) kept
  change debtOf p (locks upper j) ≤ debtOf p (endGroup group outcomes) at debt
  have creditBound := debt_credit upper j
  change 2 ≤ ownSlack p group outcomes + credit j at price
  unfold energy
  omega
#print axioms matrix
#print axioms owned_energy_two
end Owner1007.VerticalPair12
