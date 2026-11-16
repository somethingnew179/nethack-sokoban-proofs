import Owner1007.BottomCut12
import Owner1007.RightPrice4
namespace Owner1007.BottomAny12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p:=Generated.soko1_2Potential
theorem owned_credit {state final dirs pushes moves outcomes}
 (logged:Logged soko1_2.board state dirs final pushes moves outcomes)
 {history:List Dir} {past pastMoves:Nat}
 (reached:Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group:List Cell) (gUnique:group.Nodup) (subset:group⊆state.boulders)
 {i:Fin 11} (hero:state.player∈BottomCut12.region i) (inside:BottomCut12.locks i⊆group):
 BottomCut12.credit i≤energy p group outcomes:=by
 have closed:=PricedCorral.closed_of_check _ _ _ _ _ _ BottomCut12.matrix
 obtain ⟨j,_,kept,price⟩:=RightPrice4.owned_trace_price closed BottomCut12.unique logged reached group gUnique subset hero inside
 have debt:=NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (BottomCut12.locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
   (BottomCut12.unique j) kept
 change debtOf p (BottomCut12.locks j)≤debtOf p (endGroup group outcomes) at debt
 have terminal:=BottomCut12.debt_credit j
 change BottomCut12.credit j≤debtOf p (BottomCut12.locks j) at terminal
 change BottomCut12.credit i≤ownSlack p group outcomes+BottomCut12.credit j at price
 unfold energy
 omega
#print axioms owned_credit
end Owner1007.BottomAny12
