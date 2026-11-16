import Owner1007.Residual29012

namespace Owner1007.Residual290Any12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.Residual29012
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem owned_energy_credit
 (matrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p locks region credit=true)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 6) (hero : state.player∈region i) (inside : locks i⊆group) :
 credit i≤energy p group outcomes := by
 have closed := PricedCorral.closed_of_check _ _ _ _ _ _ matrix
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique logged reached group gUnique subset hero inside
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=>-p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=> by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have creditBound := debt_credit j
 change credit i≤ownSlack p group outcomes +credit j at price
 unfold energy
 omega
#print axioms owned_energy_credit
end Owner1007.Residual290Any12

