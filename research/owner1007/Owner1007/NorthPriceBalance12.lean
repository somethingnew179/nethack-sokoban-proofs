import Owner1007.EndGroupMono
import Owner1007.TwoReserves12
import Owner1007.NorthLeftBudget22712
import Owner1007.NorthLeftSurvival12
namespace Owner1007.NorthPriceBalance12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev Left := NorthLeftBudget22712.Left
theorem total {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) :
 energy p Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 := by
 have all := logged.all_energy p
 have value : p.value FirstSplit12.afterN=211 := by decide +kernel
 have empty : final.holes=[] := completed
 rw [value,empty] at all
 simp only [weightSum] at all
 have perm : (Left++Final222.R).Perm FirstSplit12.afterN.boulders := by decide +kernel
 have same := energy_perm p perm outcomes
 have split := logged.energy_split (by decide +kernel) p Left Final222.R
   (by decide +kernel) (by decide +kernel)
 simp only [Int.ofNat_eq_natCast] at all ⊢
 omega
theorem right_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) : 4≤energy p Final222.R outcomes := by
 have whole := NorthWrap12.canonical_north logged
 have right := RightPrice4.right_energy_four whole completed
 have same := (NorthWrap12.energy_north Final222.R outcomes).trans
   (congrArg (fun group=>energy p group outcomes)
     (show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel))
 change 4≤energy p Final222.R (.walk 397::.push 371 (.stay 345)::outcomes) at right
 rwa [same] at right
theorem survivor_budget {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤227) (survives : endGroup Left outcomes≠[]) :
 energy p Left outcomes≤10 := by
 have right := NorthLeftSurvival12.right_five logged completed survives
 change 5≤energy p Final222.R outcomes at right
 have all := total logged completed
 simp only [Int.ofNat_eq_natCast] at all
 omega
/-- Paid Upper4 and the existing first265 G alternative already imply229. -/
theorem upper_four_g_cases {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (upper : 4≤energy p PreCage12.U outcomes)
 (lower : 9≤energy p NorthBound12.G outcomes ∨
   (8≤energy p NorthBound12.G outcomes ∧ endGroup NorthBound12.G outcomes≠[])) :
 229≤1+pushes := by
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have joint := TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid actualUnique
   PreCage12.U NorthBound12.G Left (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change energy p PreCage12.U outcomes+energy p NorthBound12.G outcomes≤energy p Left outcomes at joint
 have all := total logged completed
 simp only [Int.ofNat_eq_natCast] at all
 rcases lower with nine|⟨eight,survives⟩
 · have right := right_four logged completed
   omega
 · have mono := logged.end_mono actualUnique NorthBound12.G Left (by decide +kernel) (by decide +kernel) (by decide +kernel)
   have alive : endGroup Left outcomes≠[] := by
     intro empty
     rw [empty] at mono
     exact survives (List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using mono member))
   have right := NorthLeftSurvival12.right_five logged completed alive
   change 5≤energy p Final222.R outcomes at right
   omega
#print axioms total
#print axioms survivor_budget
#print axioms upper_four_g_cases
end Owner1007.NorthPriceBalance12
