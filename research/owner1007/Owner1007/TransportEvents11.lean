import Owner1007.TransportQuiet11
import Owner1007.PaidCount11
namespace Owner1007.TransportEvents11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11 Owner1007.UpperQuiet11

theorem Quiet.relabel {paid forbidden state group dirs final pushes moves outcomes}
 (quiet : Quiet paid state group dirs final pushes moves outcomes)
 (region : List Cell)
 (closed : ∀source dir dest,source∈region→¬paid source dir→
   dest∈pushTargets soko1_1.board source dir→dest∈region)
 (colored : group⊆region)
 (notInside : ∀source dir,forbidden source dir→source∉region)
 (holesInside : state.holes⊆soko1_1.initial.holes) :
 Quiet forbidden state group dirs final pushes moves outcomes := by
 induction quiet with
 |nil=>exact .nil _ _
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  have one : Quiet paid state group [dir] t.state t.pushCost 1 [outcome] := .cons head effect avoid (.nil _ _)
  have nextColor := (TransportQuiet11.Quiet.transport one region closed colored false (by intro h;contradiction) holesInside).1
  change update group outcome⊆region at nextColor
  have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
  have noForbidden : ¬OwnedCorral11.PaidStep forbidden group dir t := by
   rintro ⟨source,owner,metadata,pays⟩
   exact notInside source dir pays (colored owner)
  exact .cons head effect noForbidden (ih nextColor nextHoles)

theorem count_le_ownPushes (paid : Cell→Dir→Prop) [∀c d,Decidable (paid c d)]
 (group : List Cell) (dirs : List Dir) (outcomes : List Outcome) :
 PaidCount11.count paid group dirs outcomes≤ownPushes group outcomes := by
 induction outcomes generalizing group dirs with
 |nil=>simp only [PaidCount11.count,ownPushes];omega
 |cons outcome rest ih=>
  cases dirs with
  |nil=>simp only [PaidCount11.count];omega
  |cons dir dirs=>
   have tail := ih (update group outcome) dirs
   cases outcome with
   |walk target=>
    simpa [PaidCount11.count,PaidCount11.owned,ownPushes,ownPush] using tail
   |push source ending=>
    by_cases owner : source∈group
    ·by_cases pays : paid source dir
     ·simpa [PaidCount11.count,PaidCount11.owned,owner,pays,ownPushes,ownPush] using Nat.add_le_add_left tail 1
     ·simp only [PaidCount11.count,PaidCount11.owned,pays,and_false,if_false,ownPushes,ownPush,if_pos owner,Nat.zero_add]
      omega
    ·simp only [PaidCount11.count,PaidCount11.owned,owner,false_and,if_false,ownPushes,ownPush,Nat.zero_add]
     exact tail

def FirstCut.extend {paid initial group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (cut : FirstCut paid initial group dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last) :
 FirstCut paid initial group (dirs++lastDirs) final (pushes+lastPushes) (moves+lastMoves) (outcomes++last) where
 middle := cut.middle
 actor := cut.actor
 direction := cut.direction
 headOutcome := cut.headOutcome
 beforeDirs := cut.beforeDirs
 beforePushes := cut.beforePushes
 beforeMoves := cut.beforeMoves
 beforeOutcomes := cut.beforeOutcomes
 afterDirs := cut.afterDirs++lastDirs
 afterPushes := cut.afterPushes+lastPushes
 afterMoves := cut.afterMoves+lastMoves
 afterOutcomes := cut.afterOutcomes++last
 before := cut.before
 headChecked := cut.headChecked
 headEffect := cut.headEffect
 headPaid := cut.headPaid
 after := cut.after.append suffix
 dirsEq := by simpa only [List.append_assoc,List.cons_append] using congrArg (fun middle=>middle++lastDirs) cut.dirsEq
 outcomesEq := by simpa only [List.append_assoc,List.cons_append] using congrArg (fun middle=>middle++last) cut.outcomesEq
 pushesEq := by have counts:=cut.pushesEq;omega
 movesEq := by have counts:=cut.movesEq;omega
#print axioms Quiet.relabel
#print axioms count_le_ownPushes
#print axioms FirstCut.extend
end Owner1007.TransportEvents11
