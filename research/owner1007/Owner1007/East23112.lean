import Owner1007.PreAccessFour12
import Owner1007.EastTight22912
namespace Owner1007.East23112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev H := PreAccessFour12.locks 0
abbrev R := Final222.R
def combined : List Cell := H++([371]++R)
theorem east_branch_logged_231 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterE dirs final pushes moves outcomes)
 (completed : Goal final) : 231≤1+pushes := by
 have whole := East22612.canonical_east logged
 let all := .walk 370::.push 371 (.stay 372)::outcomes
 have four := PreAccessFour12.energy_four logged East22612.east_reached H (PreAccessFour12.unique 0)
   (by decide +kernel) completed (PreAccessFour12.hero371) (fun _ h=>h)
 change 4≤energy p H outcomes at four
 have hSame := EastTight22912.initial_unaffected H (by decide +kernel) outcomes
 change energy p H all=energy p H outcomes at hSame
 have hFour : (4:Int)≤energy p H all := by omega
 have stone := East22612.stone_six logged completed
 have stoneSame := East22612.initial_stone_energy outcomes
 change 6≤energy p [372] outcomes at stone
 change energy p [371] all=2+energy p [372] outcomes at stoneSame
 have stoneEight : (8:Int)≤energy p [371] all := by omega
 have right := East22912.right_seven_suffix logged completed
 change 7≤energy p R outcomes at right
 have rSame := EastTight22912.initial_unaffected R (by decide +kernel) outcomes
 change energy p R all=energy p R outcomes at rSame
 have rightSeven : (7:Int)≤energy p R all := by omega
 have actualUnique : soko1_2.initial.boulders.Nodup := by decide +kernel
 have split1 := whole.energy_split actualUnique p H ([371]++R) (by decide +kernel) (by decide +kernel)
 change energy p combined all=energy p H all+energy p ([371]++R) all at split1
 have split2 := whole.energy_split actualUnique p [371] R (by decide +kernel) (by decide +kernel)
 change energy p ([371]++R) all=energy p [371] all+energy p R all at split2
 have mono := whole.energy_mono Generated.soko1_2_potential_valid actualUnique combined soko1_2.initial.boulders
   (by decide +kernel) actualUnique (by decide +kernel) (fun _ h=>h) (by decide +kernel)
 change energy p combined all≤energy p soko1_2.initial.boulders all at mono
 have ledger := whole.all_energy p
 have potential : p.value soko1_2.initial=212 := by decide +kernel
 have empty : final.holes=[] := completed
 rw [potential,empty] at ledger
 change 212+energy p soko1_2.initial.boulders all=Int.ofNat (1+pushes)+0 at ledger
 simp only [Int.ofNat_eq_natCast] at ledger
 omega
theorem east_branch_231 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterE dirs final pushes moves)
 (completed : Goal final) :231≤1+pushes := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact east_branch_logged_231 logged completed
#print axioms east_branch_231
end Owner1007.East23112
