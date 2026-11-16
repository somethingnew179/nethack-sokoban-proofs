import Owner1007.OwnedCorralAny11
import Owner1007.UpperQuiet11
namespace Owner1007.GrowingCorral11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.Corral11 Owner1007.PricedCorral11 Owner1007.OwnedCorral11

def Separated {n : Nat} (locks region : Fin n→List Cell) (state : State) (group top : List Cell) : Prop :=
 ∃i,state.player∈region i ∧locks i⊆group ∧∀c,c∈top→c∉region i

theorem step_separated {n : Nat} {board : Board} {holes : List Cell}
 {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : ClosedExcept board holes locks region paid) (unique : ∀i,(locks i).Nodup)
 (growth : ∀i source dir j dest,source∈locks i→dest∈pushTargets board source dir→
   locks j⊆dest::(locks i).erase source→region j⊆region i++locks i)
 {state : State} {group top : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (good : Separated locks region state group top)
 (bothUnique : (group++top).Nodup) (insideActual : group++top⊆state.boulders)
 (holesInside : state.holes⊆holes)
 (checked : step board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬PaidStep paid group dir t) :
 Separated locks region t.state (update group outcome) top ∧
 update top outcome=top ∧ownPush top outcome=0 := by
 obtain ⟨i,heroInside,inside,outside⟩ := good
 have groupInside : group⊆state.boulders := fun _ h=>insideActual (List.mem_append_left _ h)
 have actualInside : locks i⊆state.boulders := List.Subset.trans inside groupInside
 have separate := (List.nodup_append.mp bothUnique).2.2
 have smallCorner := original_corner_projected board state (locks i) actualInside dir t checked
 rcases step_cases_full board state dir t checked with walked|pushed
 ·obtain ⟨target,adjacent,floor,notBox,notHole,shape⟩ := walked
  have same := matches_unique state t (.walk target) outcome shape effect
  subst outcome
  have door := FiniteTopology.step_target_not_door board state dir t target adjacent checked
  have notLock : target∉locks i := fun h=>notBox (actualInside h)
  have targetInside := closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
  exact ⟨⟨i,by simpa only [shape] using targetInside,inside,outside⟩,rfl,rfl⟩
 ·obtain ⟨source,result,adjacent,floor,present,push,shape⟩ := pushed
  have first := push_first_clear board state source dir result push
  have spec := pushBoulder_spec board state source dir result push
  have actualEffect : Matches state t (.push source (ending result)) := by
   rcases spec.1 with stay|fill
   ·simp only [ending,stay.1]
    refine ⟨present,?_⟩
    simpa only [stay.1,stay.2,afterFill] using shape
   ·simp only [ending,fill.1]
    refine ⟨present,fill.2.1,?_⟩
    simpa only [fill.1,fill.2.2,afterFill] using shape
  have same := matches_unique state t (.push source (ending result)) outcome actualEffect effect
  subst outcome
  have notTop : source∉top := by
   intro owner
   have notLock : source∉locks i := by
    intro member
    exact separate source (inside member) source owner rfl
   have door := FiniteTopology.step_target_not_door board state dir t source adjacent checked
   have targetInside := closed.1 i state.player heroInside dir source adjacent floor door notLock smallCorner
   exact outside source owner targetInside
  have topSame : update top (.push source (ending result))=top := by simp only [update,move,if_neg notTop]
  have noOwn : ownPush top (.push source (ending result))=0 := by simp only [ownPush,if_neg notTop]
  refine ⟨?_,topSame,noOwn⟩
  by_cases member : source∈locks i
  ·have owner : source∈group := inside member
   have unpaid : ¬paid source dir := fun pays=>avoid ⟨source,owner,by simp only [shape],pays⟩
   have choice : BlockedPush board (locks i) source dir∨Shift board holes locks region i source dir := by
    rcases closed.2 i state.player heroInside dir source member adjacent with blocked|pays|shifted
    ·exact Or.inl blocked
    ·exact False.elim (unpaid pays)
    ·exact Or.inr shifted
   rcases choice with blocked|shifted
   ·rcases blocked with diagonal|blocked
    ·simp only [first.1] at diagonal
     contradiction
    ·obtain ⟨dest,next,floor,door,empty⟩ := first.2
     simp only [next] at blocked
     rcases blocked with wall|door'|box
     ·exact False.elim (wall floor)
     ·exact False.elim (door door')
     ·exact False.elim (empty (actualInside box))
   ·obtain ⟨j,dest,destFloor,targets,noHole,nextLocks,nextHero⟩ := shifted
    have landing : result.landing=dest := by simpa only [targets,List.mem_singleton] using spec.2
    have notFilled : result.filled=none := by
     rcases spec.1 with stay|fill
     ·exact stay.1
     ·exact False.elim (noHole (holesInside (landing ▸ fill.2.1)))
    have erased : (locks i).erase source⊆group.erase source := GhostSubset.erase_subset inside (unique i) source
    refine ⟨j,by simpa only [shape] using nextHero,?_,?_⟩
    ·simp only [update,move,if_pos owner,ending,notFilled,post]
     rw [landing]
     exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
    ·intro c topMember newRegion
     have oldRegion := growth i source dir j dest member destFloor nextLocks newRegion
     rcases List.mem_append.mp oldRegion with old|lock
     ·exact outside c topMember old
     ·exact separate c (inside lock) c topMember rfl
  ·have door := FiniteTopology.step_target_not_door board state dir t source adjacent checked
   have targetInside := closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
   have erased : locks i⊆group.erase source := by
    intro cell found
    have different : cell≠source := by intro same;exact member (same ▸ found)
    exact (List.mem_erase_of_ne different).mpr (inside found)
   refine ⟨i,by simpa only [shape] using targetInside,?_,outside⟩
   by_cases owner : source∈group
   ·cases filled : result.filled with
    |none=>
     simp only [update,move,if_pos owner,ending,filled,post]
     exact fun _ h=>List.mem_cons_of_mem _ (erased h)
    |some hole=>
     simpa only [update,move,if_pos owner,ending,filled,post] using erased
   ·simpa only [update,move,if_neg owner] using inside

theorem Quiet.separated_untouched {n : Nat} {holes : List Cell}
 {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : ClosedExcept soko1_1.board holes locks region paid) (unique : ∀i,(locks i).Nodup)
 (growth : ∀i source dir j dest,source∈locks i→dest∈pushTargets soko1_1.board source dir→
   locks j⊆dest::(locks i).erase source→region j⊆region i++locks i)
 {state final : State} {group top : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup)
 (bothUnique : (group++top).Nodup) (insideActual : group++top⊆state.boulders)
 (good : Separated locks region state group top) (holesInside : state.holes⊆holes) :
 Separated locks region final (endGroup group outcomes) top ∧ownPushes top outcomes=0 := by
 induction quiet with
 |nil=>exact ⟨good,rfl⟩
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  obtain ⟨nextGood,topSame,noOwn⟩ := step_separated closed unique growth good bothUnique insideActual holesInside head effect avoid
  have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
  have updatedUnique := GhostSubset.update_unique _ _ _ effect nextActual (group++top) bothUnique insideActual
  have updatedInside := GhostSubset.update_subset _ _ _ effect (group++top) bothUnique insideActual
  have perm := GhostSubset.pair_update_perm group top bothUnique outcome
  have nextUnique := perm.nodup_iff.mpr updatedUnique
  have nextInside : update group outcome++update top outcome⊆t.state.boulders :=
    fun _ h=>updatedInside (perm.mem_iff.mp h)
  rw [topSame] at nextUnique nextInside
  have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
  obtain ⟨endGood,endNoOwn⟩ := ih nextActual nextUnique nextInside nextGood nextHoles
  refine ⟨endGood,?_⟩
  simpa only [ownPushes,noOwn,topSame,Nat.zero_add] using endNoOwn
#print axioms step_separated
#print axioms Quiet.separated_untouched
end Owner1007.GrowingCorral11
