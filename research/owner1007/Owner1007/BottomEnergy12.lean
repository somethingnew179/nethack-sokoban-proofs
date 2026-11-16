import Owner1007.BottomCut12
import Owner1007.RightPrice4

namespace Owner1007.BottomEnergy12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting
abbrev raw := Generated.soko1_2Potential
def Bottom : List Cell := [318,371]

/-- Ten symbolic zero-price pair phases reserve two units of owned energy.
This holds for every original prefix, before requiring completion. -/
theorem bottom_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes) :
    2 ≤ energy raw Bottom outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ BottomCut12.matrix
  obtain ⟨j, hero, inside, price⟩ := RightPrice4.owned_trace_price closed BottomCut12.unique
    logged (Trace.nil _) Bottom (by decide +kernel) (by decide +kernel)
    (i:=0) (by decide +kernel) (by decide +kernel)
  have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -raw.boulder c)
    (BottomCut12.locks j) (endGroup Bottom outcomes)
    (fun c => by
      have h := Generated.soko1_2_potential_valid.nonpositive c
      change raw.boulder c ≤ 0 at h
      omega)
    (BottomCut12.unique j) inside
  change Owner1007.debtOf raw (BottomCut12.locks j) ≤
    Owner1007.debtOf raw (endGroup Bottom outcomes) at debt
  have credit := BottomCut12.debt_credit j
  change BottomCut12.credit j ≤ Owner1007.debtOf raw (BottomCut12.locks j) at credit
  change 2 ≤ ownSlack raw Bottom outcomes + BottomCut12.credit j at price
  unfold energy
  omega

#print axioms bottom_energy_two
end Owner1007.BottomEnergy12
