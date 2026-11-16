import Owner1007.Vertical21223812
import Owner1007.TwoReserves12
namespace Owner1007.Post265JointFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def H : List Cell := CageLedger12.Upper++[212,238]
theorem upperBonus : RightEnergy12.cert.bonus 265
 (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel

theorem core_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (hero : state.player=265) (subset : H⊆state.boulders) :
 4≤energy p H outcomes := by
 have actualUnique:=reached.boulders_nodup (by decide +kernel)
 have hUnique:H.Nodup:=by decide +kernel
 have uSubset:CageLedger12.Upper⊆state.boulders:=
   List.Subset.trans (by decide +kernel : CageLedger12.Upper⊆H) subset
 have nSubset:([212,238]:List Cell)⊆state.boulders:=
   List.Subset.trans (by decide +kernel : ([212,238]:List Cell)⊆H) subset
 have upper:=RightEnergy12.raw_group_energy logged reached CageLedger12.Upper
   (by decide +kernel) uSubset completed
 rw[hero,upperBonus] at upper
 change 2≤energy p CageLedger12.Upper outcomes at upper
 have pair:=Vertical21223812.owned_energy_two logged reached [212,238]
   (by decide +kernel) nSubset (by rw[hero];decide +kernel) (fun _ h=>h)
 change 2≤energy p [212,238] outcomes at pair
 have split:=logged.energy_split actualUnique p CageLedger12.Upper [212,238] hUnique subset
 change energy p H outcomes=energy p CageLedger12.Upper outcomes+energy p [212,238] outcomes at split
 omega

theorem energy_four {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (hero : state.player=265) (inside : H⊆group) :
 4≤energy p group outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have hSubset := List.Subset.trans inside subset
 have bound := core_four logged reached completed hero hSubset
 have mono := logged.energy_mono Generated.soko1_2_potential_valid actualUnique
   H group (by decide +kernel) gUnique hSubset subset inside
 change energy p H outcomes≤energy p group outcomes at mono
 omega

#print axioms energy_four
end Owner1007.Post265JointFour12
