import Owner1007.East22912
namespace Owner1007.EastTight22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostProjection
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
/-- The six original lower identities other than371. -/
def OtherG : List Cell := [210,237,238,263,265,318]

theorem initial_unaffected (group : List Cell) (absent : (371:Cell)∉group) (outcomes : List Outcome) :
 energy p group (.walk 370::.push 371 (.stay 372)::outcomes)=energy p group outcomes := by
 rw [energy_cons]
 simp only [projectedOutcome,slack,update,Int.zero_add]
 rw [energy_cons]
 simp only [projectedOutcome,if_neg absent,slack,update,move,Int.zero_add]

/-- Exact owned budgets for an original east-first completion with at most229
initiated pushes. These are necessary restrictions, not a229 winning witness. -/
theorem canonical_ledgers {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board EastPrice225.afterE dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤229) :
 1+pushes=229 ∧energy p Final222.U outcomes=2 ∧energy p [213] outcomes=0 ∧
 energy p Final222.R outcomes=7 ∧energy p [372] outcomes=6 ∧energy p OtherG outcomes=0 := by
 have whole := East22612.canonical_east logged
 let all := .walk 370::.push 371 (.stay 372)::outcomes
 have stone := East22612.stone_six logged completed
 have right := East22912.right_seven_suffix logged completed
 have upper := Final222.upper_energy_two whole completed
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 have remaining := whole.energy_nonnegative Generated.soko1_2_potential_valid OtherG
 have total := Final222.total_energy whole completed
 have split := whole.energy_split (by decide +kernel) p [371] OtherG
   (by decide +kernel) (by decide +kernel)
 have perm : ([371]++OtherG).Perm Final222.G := by decide +kernel
 have same := energy_perm p perm all
 have stoneSame := East22612.initial_stone_energy outcomes
 have upperSame := initial_unaffected Final222.U (by decide +kernel) outcomes
 have otherSame := initial_unaffected [213] (by decide +kernel) outcomes
 have restSame := initial_unaffected OtherG (by decide +kernel) outcomes
 have rightSame := initial_unaffected Final222.R (by decide +kernel) outcomes
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 change 2≤energy p Final222.U all at upper
 change 0≤energy p [213] all at other
 change 0≤energy p OtherG all at remaining
 change energy p ([371]++OtherG) all=energy p [371] all+energy p OtherG all at split
 change energy p [371] all=2+energy p [372] outcomes at stoneSame
 change energy p Final222.U all=energy p Final222.U outcomes at upperSame
 change energy p [213] all=energy p [213] outcomes at otherSame
 change energy p OtherG all=energy p OtherG outcomes at restSame
 change energy p Final222.R all=energy p Final222.R outcomes at rightSame
 change 7≤energy p Final222.R outcomes at right
 change 6≤energy p [372] outcomes at stone
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms initial_unaffected
#print axioms canonical_ledgers
end Owner1007.EastTight22912
