import Owner1007.TransportEvents11
namespace Owner1007.QuietAppend11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11

theorem Quiet.append {paid state group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : UpperQuiet11.Quiet paid state group dirs middle pushes moves outcomes)
 (suffix : UpperQuiet11.Quiet paid middle (endGroup group outcomes) lastDirs final lastPushes lastMoves last) :
 UpperQuiet11.Quiet paid state group (dirs++lastDirs) final (pushes+lastPushes) (moves+lastMoves) (outcomes++last) := by
 induction first with
 |nil=>simpa only [List.nil_append,Nat.zero_add,endGroup] using suffix
 |@cons state group dir t rest middle pushes moves outcome outcomes head effect avoid tail ih=>
  simpa only [List.cons_append,Nat.add_assoc] using UpperQuiet11.Quiet.cons head effect avoid (ih suffix)

def FirstCut.prepend {paid state group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (quiet : UpperQuiet11.Quiet paid state group dirs middle pushes moves outcomes)
 (cut : FirstCut paid middle (endGroup group outcomes) lastDirs final lastPushes lastMoves last) :
 FirstCut paid state group (dirs++lastDirs) final (pushes+lastPushes) (moves+lastMoves) (outcomes++last) where
 middle := cut.middle
 actor := cut.actor
 direction := cut.direction
 headOutcome := cut.headOutcome
 beforeDirs := dirs++cut.beforeDirs
 beforePushes := pushes+cut.beforePushes
 beforeMoves := moves+cut.beforeMoves
 beforeOutcomes := outcomes++cut.beforeOutcomes
 afterDirs := cut.afterDirs
 afterPushes := cut.afterPushes
 afterMoves := cut.afterMoves
 afterOutcomes := cut.afterOutcomes
 before := Quiet.append quiet cut.before
 headChecked := cut.headChecked
 headEffect := cut.headEffect
 headPaid := by rw [endGroup_append];exact cut.headPaid
 after := cut.after
 dirsEq := by simpa only [List.append_assoc] using congrArg (fun last=>dirs++last) cut.dirsEq
 outcomesEq := by simpa only [List.append_assoc] using congrArg (fun last=>outcomes++last) cut.outcomesEq
 pushesEq := by have counts:=cut.pushesEq;omega
 movesEq := by have counts:=cut.movesEq;omega
#print axioms Quiet.append
#print axioms FirstCut.prepend
end Owner1007.QuietAppend11
