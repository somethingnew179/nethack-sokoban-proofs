import Owner1007.UpperNineSurvivor11
namespace Owner1007.UpperNineOnly14111
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def D : List Cell := [137,188,193]
/-- Odd Upper9 can retain only the untouched original141; all other Upper credits saturate. -/
theorem only_141 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (nine : energy soko1_1.initial final UpperBudget11.U6 outcomes=9) :
 endGroup UpperBudget11.U6 outcomes=[141] ∧ownPushes [141] outcomes=0 ∧
 energy soko1_1.initial final [141] outcomes=7 ∧energy soko1_1.initial final TightSplit11.A outcomes=2 ∧
 energy soko1_1.initial final D outcomes=0 := by
 have pair:=PairBound11.pair_energy logged completed
 change 2≤energy soko1_1.initial final TightSplit11.A outcomes at pair
 have split:=Hero315Frame11.energy_split logged TightSplit11.A UpperBudget11.C (by decide) (by decide)
 change energy soko1_1.initial final UpperBudget11.U6 outcomes=_ at split
 have cCap : energy soko1_1.initial final UpperBudget11.C outcomes≤7 := by omega
 have debts : D.all (fun c=>decide (value soko1_1.initial [c]< -7))=true := by decide +kernel
 have goneD : endGroup D outcomes=[] := by
  apply TightSurvivors11.all_nil logged (by decide) D (by decide) (by decide)
  intro cell member
  exact TightSurvivors11.singleton_nil logged completed UpperBudget11.C (by decide) (by decide) (by decide)
   7 cCap cell ((show D⊆UpperBudget11.C by decide) member)
   (of_decide_eq_true (List.all_eq_true.mp debts cell member))
 have gone139:=UpperNineSurvivor11.gate139_gone logged completed (by omega)
 have gone191:=TightSurvivors11.singleton_nil logged completed UpperBudget11.U6 (by decide) (by decide) (by decide)
  9 (by omega) 191 (by decide) (by decide +kernel)
 have pairEnds:=HeroLedger.Logged.end_append_perm logged (by decide) [139] [191] (by decide) (by decide)
 rw[gone139,gone191] at pairEnds
 have goneA : endGroup TightSplit11.A outcomes=[] := List.perm_nil.mp pairEnds
 have ucEnds:=HeroLedger.Logged.end_append_perm logged (by decide) TightSplit11.A UpperBudget11.C (by decide) (by decide)
 rw[goneA,List.nil_append] at ucEnds
 have cPerm : UpperBudget11.C.Perm ([141]++D) := by decide +kernel
 have cEnds:=HeroLedger.Logged.end_append_perm logged (by decide) [141] D (by decide) (by decide)
 rw[goneD,List.append_nil] at cEnds
 have upperEnds : (endGroup UpperBudget11.U6 outcomes).Perm (endGroup [141] outcomes):=
  ucEnds.trans ((endGroup_perm cPerm outcomes).trans cEnds)
 have alive : endGroup [141] outcomes≠[] := by
  intro empty
  rw[empty] at upperEnds
  have goneU:=List.perm_nil.mp upperEnds
  have even:=ConsumedParity11.consumed_even logged completed UpperBudget11.U6 (by decide) (by decide) goneU
  omega
 have ledger:=survivor_energy logged completed 141 alive
 have initial : value soko1_1.initial [141]= -7 := by decide +kernel
 have mono:=energy_subset (Trace.nil soko1_1.initial) logged [141] UpperBudget11.C
  (by decide) (by decide) (by decide) (by decide) (by decide)
 rw[initial] at ledger
 simp only[Int.ofNat_eq_natCast] at ledger
 have zero : ownPushes [141] outcomes=0 := by omega
 have seven : energy soko1_1.initial final [141] outcomes=7 := by omega
 have tag141:=no_push_unchanged [141] outcomes zero
 have upTag : endGroup UpperBudget11.U6 outcomes=[141] := by
  rw[tag141] at upperEnds
  exact List.perm_singleton.mp upperEnds
 have cSplit:=Hero315Frame11.energy_split logged [141] D (by decide) (by decide)
 have cSame:=Hero315Frame11.energy_perm cPerm soko1_1.initial final outcomes
 have nn:=energy_nonnegative logged D (by decide) (by decide)
 exact ⟨upTag,zero,seven,by omega,by omega⟩
#print axioms only_141
end Owner1007.UpperNineOnly14111
