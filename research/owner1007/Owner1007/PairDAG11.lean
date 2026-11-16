import Owner1007.PairPath11
import Owner1007.PairFirstCut11
import Owner1007.PairPost11
import Owner1007.Upper190Identity11
namespace Owner1007.PairDAG11
open NetHack.Sokoban
def rank (i : Fin 9) : Nat := if i.val<5 then i.val else i.val-4
def check (i : Fin 9) : Bool := (PairPath11.locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_1.board source dir.opposite with
 | none => true
 | some hero => if hero∈PairPath11.region i then
   (List.finRange 9).all fun j => (pushTargets soko1_1.board source dir).all fun dest => decide
    (¬PairPath11.paid source dir → pushTargets soko1_1.board source dir=[dest] →
     dest∉soko1_1.initial.holes → PairPath11.locks j⊆dest::(PairPath11.locks i).erase source →
     source∈PairPath11.region j → rank j=rank i+1)
  else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked : (List.finRange 9).all check=true := by decide +kernel
#print axioms checked

open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting

theorem shift_rank (i : Fin 9) (hero source dest : Cell) (dir : Dir) (j : Fin 9)
 (heroInside : hero∈PairPath11.region i) (sourceInside : source∈PairPath11.locks i)
 (heroFloor : hero∈soko1_1.board.floor) (adjacent : advance soko1_1.board hero dir=some source)
 (unpaid : ¬PairPath11.paid source dir) (target : dest∈pushTargets soko1_1.board source dir)
 (targets : pushTargets soko1_1.board source dir=[dest]) (noHole : dest∉soko1_1.initial.holes)
 (locksNext : PairPath11.locks j⊆dest::(PairPath11.locks i).erase source)
 (heroNext : source∈PairPath11.region j) : rank j=rank i+1 := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp checked i (by simp)) source sourceInside) dir (Geometry.all_directions dir)
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero heroFloor dir source adjacent
 simp only [reverse,if_pos heroInside] at row
 have cell := List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact of_decide_eq_true cell unpaid targets noHole locksNext heroNext

theorem step_progress {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (i : Fin 9) (heroInside : state.player∈PairPath11.region i) (locksInside : PairPath11.locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤2)
 (holesInside : state.holes⊆soko1_1.initial.holes)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬OwnedCorral11.PaidStep PairPath11.paid group dir t) :
 ∃ j : Fin 9, t.state.player∈PairPath11.region j ∧ PairPath11.locks j⊆update group outcome ∧
   rank j=rank i+ownPush group outcome := by
 have actualInside : PairPath11.locks i⊆state.boulders := List.Subset.trans locksInside inside
 have smallCorner := original_corner_projected soko1_1.board state (PairPath11.locks i) actualInside dir t head
 rcases step_cases_full soko1_1.board state dir t head with walked|pushed
 · obtain ⟨target,adjacent,floor,notBox,notHole,shape⟩ := walked
   have same := matches_unique state t (.walk target) outcome shape effect
   subst outcome
   have door := FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
   have notLock : target∉PairPath11.locks i := fun h => notBox (actualInside h)
   have nextHero := PairPath11.closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
   exact ⟨i,by simpa only [shape] using nextHero,locksInside,by simp only [ownPush,Nat.add_zero]⟩
 · obtain ⟨source,result,adjacent,floor,present,push,shape⟩ := pushed
   have first := push_first_clear soko1_1.board state source dir result push
   have spec := pushBoulder_spec soko1_1.board state source dir result push
   have actualEffect : Matches state t (.push source (ending result)) := by
     rcases spec.1 with stay|fill
     · simp only [ending,stay.1]
       refine ⟨present,?_⟩
       simpa only [stay.1,stay.2,afterFill] using shape
     · simp only [ending,fill.1]
       refine ⟨present,fill.2.1,?_⟩
       simpa only [fill.1,fill.2.2,afterFill] using shape
   have same := matches_unique state t (.push source (ending result)) outcome actualEffect effect
   subst outcome
   by_cases member : source∈PairPath11.locks i
   · have owner := locksInside member
     have unpaid : ¬PairPath11.paid source dir := by
       intro pays
       exact avoid ⟨source,owner,by simp only [shape],pays⟩
     have choice : BlockedPush soko1_1.board (PairPath11.locks i) source dir ∨
         Corral11.Shift soko1_1.board soko1_1.initial.holes PairPath11.locks PairPath11.region i source dir := by
       rcases PairPath11.closed.2 i state.player heroInside dir source member adjacent with blocked|paid|shift
       · exact Or.inl blocked
       · exact False.elim (unpaid paid)
       · exact Or.inr shift
     rcases choice with blocked|shifted
     · rcases blocked with diagonal|blocked
       · simp only [first.1] at diagonal
         contradiction
       · obtain ⟨dest,next,floor,door,empty⟩ := first.2
         simp only [next] at blocked
         rcases blocked with wall|door'|box
         · exact False.elim (wall floor)
         · exact False.elim (door door')
         · exact False.elim (empty (actualInside box))
     · obtain ⟨j,dest,destFloor,targets,noHole,nextLocks,nextHero⟩ := shifted
       have landing : result.landing=dest := by simpa only [targets,List.mem_singleton] using spec.2
       have notFilled : result.filled=none := by
         rcases spec.1 with stay|fill
         · exact stay.1
         · exact False.elim (noHole (holesInside (landing ▸ fill.2.1)))
       have erased : (PairPath11.locks i).erase source⊆group.erase source :=
         GhostSubset.erase_subset locksInside (PairPath11.unique i) source
       have count := shift_rank i state.player source dest dir j heroInside member
         (step_player_clear _ _ _ _ head).1 adjacent unpaid destFloor targets noHole nextLocks nextHero
       refine ⟨j,by simpa only [shape] using nextHero,?_,?_⟩
       · simp only [update,move,if_pos owner,ending,notFilled,post]
         rw [landing]
         exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
       · simpa only [ownPush,if_pos owner] using count
   · have noOwner : source∉group := by
       intro owner
       have all : source::PairPath11.locks i⊆group := by
         intro c found
         rcases List.mem_cons.mp found with rfl|later
         · exact owner
         · exact locksInside later
       have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,PairPath11.unique i⟩) all
       simp only [List.length_cons,PairPath11.size i] at card
       omega
     have door := FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
     have nextHero := PairPath11.closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
     refine ⟨i,by simpa only [shape] using nextHero,?_,?_⟩
     · simpa only [update,move,if_neg noOwner] using locksInside
     · simp only [ownPush,if_neg noOwner,Nat.add_zero]

theorem quiet_progress {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet PairPath11.paid state group dirs final pushes moves outcomes)
 (actualUnique : state.boulders.Nodup) (unique : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤2) (i : Fin 9) (heroInside : state.player∈PairPath11.region i)
 (locksInside : PairPath11.locks i⊆group) (holesInside : state.holes⊆soko1_1.initial.holes) :
 ∃ j : Fin 9, final.player∈PairPath11.region j ∧ PairPath11.locks j⊆endGroup group outcomes ∧
   rank j=rank i+ownPushes group outcomes := by
 induction quiet generalizing i with
 | nil => exact ⟨i,heroInside,locksInside,by simp only [ownPushes,Nat.add_zero]⟩
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   obtain ⟨j,nextHero,nextLocks,nextRank⟩ := step_progress i heroInside locksInside inside bounded holesInside head effect avoid
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   obtain ⟨k,lastHero,lastLocks,lastRank⟩ := ih nextActual nextUnique nextInside nextBound j nextHero nextLocks nextHoles
   refine ⟨k,lastHero,lastLocks,?_⟩
   simp only [ownPushes]
   omega
#print axioms step_progress
#print axioms quiet_progress


theorem ownPushes_subset {board initial dirs final pushes moves outcomes}
 (logged : Logged board initial dirs final pushes moves outcomes)
 (actualUnique : initial.boulders.Nodup)
 (small big : List Cell) (smallUnique : small.Nodup) (bigUnique : big.Nodup)
 (inside : big⊆initial.boulders) (subset : small⊆big) :
 ownPushes small outcomes≤ownPushes big outcomes := by
 induction logged generalizing small big with
 | nil => exact Nat.le_refl 0
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   have smallInside := List.Subset.trans subset inside
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
   have nextSmallUnique := GhostSubset.update_unique _ _ _ effect nextActual small smallUnique smallInside
   have nextBigUnique := GhostSubset.update_unique _ _ _ effect nextActual big bigUnique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect big bigUnique inside
   have nextSubset := update_mono small big smallUnique subset outcome
   have later := ih nextActual (update small outcome) (update big outcome) nextSmallUnique nextBigUnique nextInside nextSubset
   have first : ownPush small outcome≤ownPush big outcome := by
     cases outcome with
     | walk _ => exact Nat.le_refl 0
     | push source ending =>
       by_cases owner : source∈small
       · simp [ownPush,owner,subset owner]
       · simp only [ownPush,if_neg owner]
         exact Nat.zero_le _
   simp only [ownPushes]
   omega

theorem pair_one {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs state pushes moves outcomes)
 (endpoint : (endGroup PairFirstCut11.originalGroup outcomes).Perm [138,191] ∨
   (endGroup PairFirstCut11.originalGroup outcomes).Perm [139,190]) :
 ownPushes PairFirstCut11.originalGroup outcomes=1 := by
 obtain ⟨j,heroInside,locksInside,progress⟩ := quiet_progress quiet (by decide) (by decide) (by decide) (by decide)
   0 (by decide +kernel) (by decide) (by simp)
 have selected := quiet.logged.end_subset (by decide) PairFirstCut11.originalGroup (by decide) (by decide)
 have bounded := endGroup_length_le PairFirstCut11.originalGroup outcomes
 have canonical := PairPost11.canonical_group j _ selected.1 bounded locksInside
 have rankOne : rank j=1 := by
   have all : (List.finRange 9).all (fun i => decide
     ((PairPath11.locks i).Perm [138,191] ∨ (PairPath11.locks i).Perm [139,190] → rank i=1))=true := by decide +kernel
   apply of_decide_eq_true (List.all_eq_true.mp all j (by simp))
   rcases endpoint with first|second
   · exact Or.inl (canonical.symm.trans first)
   · exact Or.inr (canonical.symm.trans second)
 have zero : rank 0=0 := rfl
 omega

theorem before138 {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs state pushes moves outcomes)
 (endpoint : (endGroup PairFirstCut11.originalGroup outcomes).Perm [138,191]) :
 ownPushes [139] outcomes≤1 ∧ endGroup [139] outcomes=[138] := by
 have pairCount := pair_one quiet (Or.inl endpoint)
 have bound := ownPushes_subset quiet.logged (by decide) [139] PairFirstCut11.originalGroup (by decide) (by decide) (by decide) (by decide)
 have present191 : 191∈endGroup PairFirstCut11.originalGroup outcomes := endpoint.mem_iff.mpr (by simp)
 have still191 := (OneWayToken11.historical quiet.logged (by decide) 191 PairFirstCut11.originalGroup (by decide) (by decide)
   (PairFirstCut11.quiet_no_return quiet (by decide) (by decide) (by decide) (by decide) PairFirstCut11.initial_good (by simp) 191 (by decide)) present191).2
 have split := HeroLedger.Logged.end_append_perm quiet.logged (by decide) [139] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ still191] at split
 have present138 : 138∈endGroup [139] outcomes := by
   have member : 138∈endGroup PairFirstCut11.originalGroup outcomes := endpoint.mem_iff.mpr (by simp)
   simpa using split.mem_iff.mp member
 have tag := Upper190Identity11.singleton_member _ 138 (Nat.le_trans (endGroup_length_le [139] outcomes) (by simp)) present138
 exact ⟨by omega,tag⟩

theorem before190 {dirs state pushes moves outcomes}
 (quiet : UpperQuiet11.Quiet PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs state pushes moves outcomes)
 (endpoint : (endGroup PairFirstCut11.originalGroup outcomes).Perm [139,190]) :
 ownPushes [191] outcomes≤1 ∧ endGroup [191] outcomes=[190] := by
 have pairCount := pair_one quiet (Or.inr endpoint)
 have bound := ownPushes_subset quiet.logged (by decide) [191] PairFirstCut11.originalGroup (by decide) (by decide) (by decide) (by decide)
 have present139 : 139∈endGroup PairFirstCut11.originalGroup outcomes := endpoint.mem_iff.mpr (by simp)
 have still139 := (OneWayToken11.historical quiet.logged (by decide) 139 PairFirstCut11.originalGroup (by decide) (by decide)
   (PairFirstCut11.quiet_no_return quiet (by decide) (by decide) (by decide) (by decide) PairFirstCut11.initial_good (by simp) 139 (by decide)) present139).2
 have split := HeroLedger.Logged.end_append_perm quiet.logged (by decide) [139] [191] (by decide) (by decide)
 rw [no_push_unchanged _ _ still139] at split
 have present190 : 190∈endGroup [191] outcomes := by
   have member : 190∈endGroup PairFirstCut11.originalGroup outcomes := endpoint.mem_iff.mpr (by simp)
   simpa using split.mem_iff.mp member
 have tag := Upper190Identity11.singleton_member _ 190 (Nat.le_trans (endGroup_length_le [191] outcomes) (by simp)) present190
 exact ⟨by omega,tag⟩
#print axioms before138
#print axioms before190

end Owner1007.PairDAG11
