import Owner1007.RightPrice4
namespace Owner1007.Corner320Two12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 4→List Cell |0=>[320,345] |1=>[320,319] |2=>[320,293] |3=>[]
def region (i : Fin 4) : List Cell :=
 soko1_2.board.floor.filter fun c=>!(locks i).contains c && (if i=2 then decide (c≠294) else true)
def credit (i : Fin 4) : Int := if i=3 then 0 else 2
theorem matrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p locks region credit=true := by decide +kernel
theorem closed : PricedCorral.Closed soko1_2.board soko1_2.initial.holes p locks region credit :=
 PricedCorral.closed_of_check _ _ _ _ _ _ matrix
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i,credit i≤debtOf p (locks i) := by decide +kernel
theorem hero319 : (319:Cell)∈region 0∧(319:Cell)∈region 2 := by decide +kernel

theorem owned_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 {i : Fin 4} (positive : credit i=2) (hero : state.player∈region i) (inside : locks i⊆group) :
 2≤energy p group outcomes := by
 obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price closed unique
   logged reached group gUnique subset hero inside
 have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c=> -p.boulder c)
   (locks j) (endGroup group outcomes)
   (fun c=>by have h:=Generated.soko1_2_potential_valid.nonpositive c;change p.boulder c≤0 at h;omega)
   (unique j) kept
 change debtOf p (locks j)≤debtOf p (endGroup group outcomes) at debt
 have creditBound := debt_credit j
 rw [positive] at price
 change 2≤ownSlack p group outcomes+credit j at price
 unfold energy
 omega
#print axioms matrix
#print axioms owned_two
end Owner1007.Corner320Two12
