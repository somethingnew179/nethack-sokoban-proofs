import Owner1007.AfterForwardSeven11Data
namespace Owner1007.AfterForwardSeven11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem one_step {beforeDirs state beforePushes beforeMoves before group dir t outcome dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (tail : Logged soko1_1.board t.state dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : beforePushes+t.pushCost+pushes≤327)
 (i : Fin 7) (same : group.Perm (locks i)) (inside : group⊆state.boulders) (hero : state.player∈region i)
 (avoid : ¬OwnedCorral11.PaidStep paid group dir t) :
 ∃j : Fin 7,(update group outcome).Perm (locks j)∧
 update [left i] outcome=[left j]∧update [upper i] outcome=[upper j]∧update [right i] outcome=[right j]∧
 t.state.player∈region j := by
 have physical : locks i⊆state.boulders := fun c member=>inside (same.mem_iff.mpr member)
 have smallCorner := original_corner_projected soko1_1.board state (locks i) physical dir t head
 rcases step_cases_full soko1_1.board state dir t head with walked|pushed
 ·obtain ⟨target,adjacent,isFloor,notBox,notHole,form⟩:=walked
  have outEq := matches_unique state t (.walk target) outcome form effect
  subst outcome
  have door:=FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
  have nextHero := walk_closed i state.player hero dir target adjacent isFloor door
   (fun member=>notBox (physical member)) smallCorner
  exact ⟨i,same,rfl,rfl,rfl,by simpa only [form] using nextHero⟩
 ·obtain ⟨source,result,adjacent,isFloor,present,push,form⟩:=pushed
  have spec := pushBoulder_spec _ _ _ _ _ push
  have actualEffect : Matches state t (.push source (ending result)) := by
   rcases spec.1 with stay|fill
   ·simp only [ending,stay.1]
    refine ⟨present,?_⟩
    simpa only [stay.1,stay.2,afterFill] using form
   ·simp only [ending,fill.1]
    refine ⟨present,fill.2.1,?_⟩
    simpa only [fill.1,fill.2.2,afterFill] using form
  have outEq:=matches_unique state t (.push source (ending result)) outcome actualEffect effect
  subst outcome
  by_cases member : source∈locks i
  ·have row:=shape i state.player source result.landing dir hero member adjacent spec.2
   have noFill : result.filled=none := by
    rcases spec.1 with stay|fill
    ·exact stay.1
    ·exact False.elim (row.1 (first.trace.holes_sublist.subset fill.2.1))
   have metadata : t.pushSource=some source := by simp only [form]
   have actualEnding : Outcome.push source (ending result)=Outcome.push source (.stay result.landing) := by simp only [ending,noFill]
   rcases row.2 with blocked|shape
   ·exact False.elim (WestRankHead11.source_unblocked head metadata physical blocked)
   ·rcases shape with pays|next|dead
    ·exact False.elim (avoid ⟨source,same.mem_iff.mpr member,metadata,pays⟩)
    ·obtain ⟨j,nextPerm,leftEq,upperEq,rightEq,nextHero⟩:=next
     refine ⟨j,?_,?_,?_,?_,?_⟩
     ·rw [actualEnding]
      exact (update_perm same _).trans nextPerm
     ·rw [actualEnding];exact leftEq
     ·rw [actualEnding];exact upperEq
     ·rw [actualEnding];exact rightEq
     ·simpa only [form] using nextHero
    ·obtain ⟨k,lockedInside⟩:=dead
     let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [.push source (ending result)] :=
      .cons head actualEffect (.nil _)
     let extended:=first.append one
     have selectedInside:=GhostSubset.update_subset state t (.push source (ending result)) actualEffect
      (locks i) (unique i) physical
     have deadPhysical : frozen k⊆t.state.boulders := List.Subset.trans
      (by simpa only [actualEnding] using lockedInside) selectedInside
     obtain ⟨k,bound⟩:=k
     have choices : k=0∨k=1∨k=2∨k=3 := by omega
     rcases choices with rfl|rfl|rfl|rfl
     ·exact False.elim (LeftTwoLaneForward11.frozen185186 extended tail completed cheap deadPhysical)
     ·exact False.elim (TightRowPairs32711.excluded extended tail completed cheap 0 deadPhysical)
     ·exact False.elim (TightRowPairs32711.excluded extended tail completed cheap 1 deadPhysical)
     ·exact False.elim (TightRowPairs32711.excluded extended tail completed cheap 2 deadPhysical)
  ·have notGroup : source∉group := fun owner=>member (same.mem_iff.mp owner)
   have notLeft : source∉[left i] := by
    intro found
    have eq : source=left i:=List.mem_singleton.mp found
    exact member (by simp [locks,eq])
   have notUpper : source∉[upper i] := by
    intro found
    have eq : source=upper i:=List.mem_singleton.mp found
    exact member (by simp [locks,eq])
   have notRight : source∉[right i] := by
    intro found
    have eq : source=right i:=List.mem_singleton.mp found
    exact member (by simp [locks,eq])
   have door:=FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
   have nextHero:=walk_closed i state.player hero dir source adjacent isFloor door member smallCorner
   refine ⟨i,?_,?_,?_,?_,?_⟩
   ·simpa only [update,move,if_neg notGroup] using same
   ·simp only [update,move,if_neg notLeft]
   ·simp only [update,move,if_neg notUpper]
   ·simp only [update,move,if_neg notRight]
   ·simpa only [form] using nextHero
#print axioms one_step
end Owner1007.AfterForwardSeven11

namespace Owner1007.AfterForwardSeven11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem quiet_word {beforeDirs state beforePushes beforeMoves before group dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (quiet : UpperQuiet11.Quiet paid state group dirs middle pushes moves outcomes)
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : beforePushes+pushes+lastPushes≤327)
 (i : Fin 7) (same : group.Perm (locks i)) (inside : group⊆state.boulders) (hero : state.player∈region i) :
 ∃j : Fin 7,(endGroup group outcomes).Perm (locks j)∧
 endGroup [left i] outcomes=[left j]∧endGroup [upper i] outcomes=[upper j]∧endGroup [right i] outcomes=[right j]∧middle.player∈region j := by
 induction quiet generalizing beforeDirs beforePushes beforeMoves before i with
 |nil=>exact ⟨i,same,rfl,rfl,rfl,hero⟩
 |@cons state group dir t rest middle pushes moves outcome outcomes head effect avoid tail ih=>
  have nextCheap : beforePushes+t.pushCost+(pushes+lastPushes)≤327 := by omega
  obtain ⟨j,nextSame,leftEq,upperEq,rightEq,nextHero⟩:=one_step first head effect (tail.logged.append suffix) completed nextCheap i same inside hero avoid
  have oldUnique := same.nodup_iff.mpr (unique i)
  have nextInside := GhostSubset.update_subset _ _ _ effect group oldUnique inside
  let one : Logged soko1_1.board state [dir] t.state t.pushCost 1 [outcome] := .cons head effect (.nil _)
  let nextFirst := first.append one
  have afterCheap : beforePushes+t.pushCost+pushes+lastPushes≤327 := by omega
  obtain ⟨k,lastSame,lastLeft,lastUpper,lastRight,lastHero⟩:=ih nextFirst suffix afterCheap j nextSame nextInside nextHero
  exact ⟨k,lastSame,by simpa only [endGroup,leftEq] using lastLeft,
   by simpa only [endGroup,upperEq] using lastUpper,by simpa only [endGroup,rightEq] using lastRight,lastHero⟩
theorem first_cut {beforeDirs state beforePushes beforeMoves before group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤327)
 (i : Fin 7) (same : group.Perm (locks i)) (inside : group⊆state.boulders) (hero : state.player∈region i) :
 Nonempty (FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged group with found|quiet
 ·exact found
 ·obtain ⟨j,lastSame,_,_,_,_⟩:=quiet_word quiet first (.nil _) completed (by omega) i same inside hero
  have actual := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
  have finalInside := (logged.end_subset actual.1 group (same.nodup_iff.mpr (unique i)) inside).2
  have physical : locks j⊆final.boulders := fun c member=>finalInside (lastSame.mem_iff.mpr member)
  have card := List.Nodup.length_le_of_subset (unique j) physical
  have conservation := (first.trace.append logged.trace).conservation
  have empty : final.holes=[]:=completed
  rw [empty] at conservation
  rw [size j] at card
  change 18+0=final.boulders.length+16 at conservation
  omega
theorem first_packet {beforeDirs state beforePushes beforeMoves before group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤327)
 (i : Fin 7) (same : group.Perm (locks i)) (inside : group⊆state.boulders) (hero : state.player∈region i) :
 ∃cut : FirstCut paid state group dirs final pushes moves outcomes,∃j : Fin 7,
 (endGroup group cut.beforeOutcomes).Perm (locks j)∧
 endGroup [left i] cut.beforeOutcomes=[left j]∧endGroup [upper i] cut.beforeOutcomes=[upper j]∧
 endGroup [right i] cut.beforeOutcomes=[right j]∧cut.middle.player∈region j := by
 obtain ⟨cut⟩:=first_cut first logged completed cheap i same inside hero
 have beforeCheap : beforePushes+cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤327 := by
  have counts:=cut.pushesEq
  omega
 obtain ⟨j,beforeSame,leftEq,upperEq,rightEq,beforeHero⟩:=quiet_word cut.before first
  (Logged.cons cut.headChecked cut.headEffect cut.after) completed beforeCheap i same inside hero
 exact ⟨cut,j,beforeSame,leftEq,upperEq,rightEq,beforeHero⟩
def HeadShape (i : Fin 7) (source : Cell) (dir : Dir) : Prop :=
 ((source=137∨source=139)∧i.val=0)∨
 (source=left i∧dir=.west)∨
 (source=upper i∧(source=187∨source=188)∧dir=.west)∨
 (source=right i∧source=190∧(dir=.north∨dir=.east))
instance (i : Fin 7) (source : Cell) (dir : Dir) : Decidable (HeadShape i source dir) := by unfold HeadShape;infer_instance
def headCheck (i : Fin 7) : Bool := (locks i).all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∈region i→¬BlockedPush soko1_1.board (locks i) source dir→paid source dir→HeadShape i source dir)
theorem heads : (List.finRange 7).all headCheck=true := by decide +kernel
theorem head_shape {state : State} {dir : Dir} {t : Transition} {group : List Cell}
 (i : Fin 7) (same : group.Perm (locks i)) (inside : group⊆state.boulders) (hero : state.player∈region i)
 (head : step soko1_1.board state dir=some t) (pays : OwnedCorral11.PaidStep paid group dir t) :
 ∃source,source∈group∧t.pushSource=some source∧HeadShape i source dir := by
 obtain ⟨source,owner,metadata,pays⟩:=pays
 have member:=same.mem_iff.mp owner
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have adjacent:=PairPost11.source_adjacent head metadata
 have reverse:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,reverse] at row
 exact ⟨source,owner,metadata,of_decide_eq_true row hero
  (WestRankHead11.source_unblocked head metadata (List.Subset.trans (fun c h=>same.mem_iff.mpr h) inside)) pays⟩
#print axioms quiet_word
#print axioms first_packet
#print axioms head_shape
end Owner1007.AfterForwardSeven11
