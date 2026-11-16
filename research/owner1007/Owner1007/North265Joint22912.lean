import Owner1007.Post265JointFour12
import Owner1007.North265LowerOwnership12
import Owner1007.NorthPriceBalance12
import Owner1007.TwoReserves12
import Owner1007.EndGroupMono
namespace Owner1007.North265Joint22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Joint : List Cell := CageLedger12.Upper++[213,238]
theorem joint_reserve {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape : outcomes=before++(.push 265 (.stay 291))::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (upper : endGroup CageLedger12.Upper before=CageLedger12.Upper)
 (sAt : endGroup [213] before=[212])
 (fixed : ∀ small : List Cell, small⊆NorthEvents12.J→endGroup small before=small) :
 4≤energy p Joint outcomes := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have middleReached := NorthBound12.north_reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have old := first.end_subset initialUnique Joint (by decide +kernel) (by decide +kernel)
 have a := first.end_split initialUnique [213] [238] (by decide +kernel) (by decide +kernel)
 rw[sAt,fixed [238] (by decide +kernel)] at a
 have b := first.end_split initialUnique CageLedger12.Upper [213,238] (by decide +kernel) (by decide +kernel)
 rw[upper] at b
 have together := (List.Perm.refl CageLedger12.Upper).append a
 have perm : Post265JointFour12.H.Perm (endGroup Joint before) := together.trans b
 have ownerFalse : (265:Cell)∉endGroup Joint before := by
   intro h
   have inside := perm.mem_iff.mpr h
   exact (by decide +kernel : (265:Cell)∉Post265JointFour12.H) inside
 have hMiddle : Post265JointFour12.H⊆middle.boulders :=
   List.Subset.trans (fun _ h=>perm.mem_iff.mp h) old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have nextSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
   Post265JointFour12.H (by decide +kernel) hMiddle
 have unchanged : update Post265JointFour12.H (.push 265 (.stay 291))=Post265JointFour12.H := by decide +kernel
 rw[unchanged] at nextSubset
 have hero : t.state.player=265 := matches_hero middle t (.push 265 (.stay 291)) effect
 have later := Post265JointFour12.core_four last nextReached completed hero nextSubset
 have same := energy_perm p perm after
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid Joint
 change 0≤ownSlack p Joint before at prefixNN
 rw[shape,energy_at_split]
 simp only[projectedOutcome,if_neg ownerFalse,slack,update,move,if_neg ownerFalse]
 change 4≤ownSlack p Joint before+0+energy p (endGroup Joint before) after
 change energy p Post265JointFour12.H after=energy p (endGroup Joint before) after at same
 change 4≤energy p Post265JointFour12.H after at later
 omega

theorem first265_lower229 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape : outcomes=before++(.push 265 (.stay 291))::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i : Fin 5)
 (fixed : ∀ small : List Cell, small⊆NorthEvents12.J→endGroup small before=small)
 (tag : endGroup [345] before=[NorthEvents12.current i])
 (upper : endGroup CageLedger12.Upper before=CageLedger12.Upper)
 (sAt : endGroup [213] before=[212]) :
 229≤1+pushes := by
 have h4 := joint_reserve logged completed shape first checked effect last upper sAt fixed
 have lower := North265LowerOwnership12.first265_lower_cases logged completed shape first checked effect last i fixed tag
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have sum := TwoReserves12.add_le_energy logged Generated.soko1_2_potential_valid actualUnique
   Joint North265LowerOwnership12.Lower NorthPriceBalance12.Left
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change energy p Joint outcomes+energy p North265LowerOwnership12.Lower outcomes≤energy p NorthPriceBalance12.Left outcomes at sum
 have total := NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 simp only[Int.ofNat_eq_natCast] at total
 change 9≤energy p North265LowerOwnership12.Lower outcomes ∨ (8≤energy p North265LowerOwnership12.Lower outcomes ∧ endGroup North265LowerOwnership12.Lower outcomes≠[]) at lower
 rcases lower with nine|⟨eight,survives⟩
 · have right := NorthPriceBalance12.right_four logged completed
   change 4≤energy p Final222.R outcomes at right
   omega
 · have mono := logged.end_mono actualUnique North265LowerOwnership12.Lower NorthPriceBalance12.Left
     (by decide +kernel) (by decide +kernel) (by decide +kernel)
   have alive : endGroup NorthPriceBalance12.Left outcomes≠[] := by
     intro empty
     rw[empty] at mono
     exact survives (List.eq_nil_iff_forall_not_mem.mpr (by intro c member;simpa using mono member))
   have right := NorthLeftSurvival12.right_five logged completed alive
   change 5≤energy p Final222.R outcomes at right
   omega
#print axioms joint_reserve
#print axioms first265_lower229
end Owner1007.North265Joint22912
