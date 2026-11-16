import Owner1007.Triangle29111Prices
import Owner1007.LoggedEventGap11
namespace Owner1007.Deep29133511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem pushes_lower {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .south=some t) (effect : Matches state t (.push 291 (.stay 317)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final) :
 335≤beforePushes+t.pushCost+afterPushes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) soko1_1.initial.boulders (by decide) (by decide)
 have owner : 291∈endGroup soko1_1.initial.boulders before := by
   rw [HeroLedger.Logged.end_all first]
   exact effect.1
 have metadata : t.pushSource=some 291 := by rw [effect.2]
 have row := Triangle29111.exit_row valid selected.1 selected.2 head effect owner metadata
   (show Triangle29111.paid 291 .south from by decide)
 change 20≤charge NetHack.Soko11Hero315.holeWeight (endGroup soko1_1.initial.boulders before) (.push 291 (.stay 317))+
   value t.state (update (endGroup soko1_1.initial.boulders before) (.push 291 (.stay 317)))-
   value state (endGroup soko1_1.initial.boulders before) at row
 have bound := logged_event_gap_le first head effect last soko1_1.initial.boulders (by decide) (by decide)
 let logged := first.append (Logged.cons head effect last)
 have total := total_energy logged completed
 change energy soko1_1.initial final soko1_1.initial.boulders (before++.push 291 (.stay 317)::after)=
   Int.ofNat (beforePushes+(t.pushCost+afterPushes))-315 at total
 simp only [Int.ofNat_eq_natCast,Int.natCast_add] at total
 omega
#print axioms pushes_lower
end Owner1007.Deep29133511
