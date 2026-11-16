import Owner1007.NorthBound12
import Owner1007.NorthWrap12
import Owner1007.Final222
import Owner1007.RightCapacity12
namespace Owner1007.NorthBudget22312
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
abbrev U := Final222.U
abbrev S : List Cell := [213]
abbrev R := Final222.R
abbrev G := NorthBound12.G

theorem budget {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤223) :
 energy p U outcomes + energy p S outcomes≤3 ∧ energy p S outcomes≤1 ∧ energy p G outcomes≤5 := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have sameU : energy p U all=energy p U outcomes := by
   exact (NorthWrap12.energy_north U outcomes).trans (congrArg (fun group => energy p group outcomes)
     (show update U (.push 371 (.stay 345))=U by decide +kernel))
 have sameS : energy p S all=energy p S outcomes := by
   exact (NorthWrap12.energy_north S outcomes).trans (congrArg (fun group => energy p group outcomes)
     (show update S (.push 371 (.stay 345))=S by decide +kernel))
 have sameR : energy p R all=energy p R outcomes := by
   exact (NorthWrap12.energy_north R outcomes).trans (congrArg (fun group => energy p group outcomes)
     (show update R (.push 371 (.stay 345))=R by decide +kernel))
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm G := by decide +kernel
 have sameG : energy p Final222.G all=energy p G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have total := Final222.total_energy whole completed
 change energy p U all + energy p Final222.G all + energy p S all + energy p R all =
   Int.ofNat (1+pushes)-212 at total
 rw [sameU,sameS,sameR,sameG] at total
 simp only [Int.ofNat_eq_natCast] at total
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p U all at upper
 rw [sameU] at upper
 have right := RightPrice4.right_energy_four whole completed
 change 4≤energy p R all at right
 rw [sameR] at right
 have nnS := logged.energy_nonnegative Generated.soko1_2_potential_valid S
 change 0≤energy p S outcomes at nnS
 rcases NorthBound12.g_cases logged completed with four | ⟨three,survives⟩
 · change 4≤energy p G outcomes at four
   omega
 · have survivesWhole : endGroup [318] all≠[] := by
     change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
     have unchanged : update [318] (.push 371 (.stay 345))=[318] := by decide +kernel
     rw [unchanged]
     exact survives
   have five := RightCapacity12.right_energy_five_of318survives whole completed survivesWhole
   change 5≤energy p R all at five
   rw [sameR] at five
   change 3≤energy p G outcomes at three
   omega
#print axioms budget
end Owner1007.NorthBudget22312
