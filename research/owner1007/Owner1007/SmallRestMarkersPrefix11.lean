import Owner1007.GateMarkersPrefix11
import Owner1007.SmallRestBelow11
import Owner1007.SmallRestFront11
namespace Owner1007.SmallRestMarkersPrefix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem stationary {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (quiet : UpperQuiet11.Quiet Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes)
 (cell : Cell) (member : cell∈([264,266] : List Cell)) :
 ownPushes [cell] outcomes=0 := by
 let full := prefixLog.append suffix
 rcases first_cut_or_quiet (paid:=Gate265Transport11.paid) suffix (endGroup soko1_1.initial.boulders outcomes) with found|quietTail
 ·obtain ⟨later⟩ := found
  let global := QuietAppend11.FirstCut.prepend quiet later
  have stationary := SmallRestMarkers11.stationary_before full zeroRest global cell member
  change ownPushes [cell] (outcomes++later.beforeOutcomes)=0 at stationary
  rw [ownPushes_append] at stationary
  omega
 ·have quietFull := QuietAppend11.Quiet.append quiet quietTail
  have countZero := FirstRest18711.quiet_count_zero quietFull
  obtain ⟨global⟩ := Gate265Transport11.first_cut full completed
  have event := PaidCount11.event_le (paid:=Gate265Transport11.paid)
    (lastDirs:=global.afterDirs) (last:=global.afterOutcomes) global.before.logged global.headEffect
    soko1_1.initial.boulders global.headPaid
  rw [←global.dirsEq,←global.outcomesEq,countZero] at event
  omega
#print axioms stationary
end Owner1007.SmallRestMarkersPrefix11
