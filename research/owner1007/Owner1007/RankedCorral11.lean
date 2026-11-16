import Owner1007.CutStrict11
import Owner1007.OwnedCorral11
import Owner1007.UpperFirstCut11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.RankedCorral11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

def Refinement {n : Nat} (locks region : Fin n→List Cell) (marker : Fin n→Cell) (rank : Fin n→Int)
 (paid : Cell→Dir→Prop) : Prop :=
 ∀ i hero source dest dir j,
 hero∈region i → source∈locks i → advance soko1_1.board hero dir=some source →
 dir.diagonal=false → ¬paid source dir →
 dest∈pushTargets soko1_1.board source dir → pushTargets soko1_1.board source dir=[dest] →
 dest∉soko1_1.initial.holes → locks j⊆dest::(locks i).erase source → source∈region j →
 update [marker i] (.push source (.stay dest))=[marker j] ∧
 (rank j≤rank i ∨ (rank j≤rank i+2 ∧ CutActor11.Exit source dir))

def gap (state : State) (t : Transition) (group : List Cell) (outcome : Outcome) : Int :=
 charge NetHack.Soko11Hero315.holeWeight group outcome + value t.state (update group outcome)-value state group

theorem step_rank {n k : Nat} {locks region : Fin n→List Cell} {marker : Fin n→Cell}
 {rank : Fin n→Int} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (unique : ∀i, (locks i).Nodup) (size : ∀i, (locks i).length=k)
 (markerInside : ∀i, marker i∈locks i) (refined : Refinement locks region marker rank paid)
 {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (i : Fin n) (heroInside : state.player∈region i) (locksInside : locks i⊆group)
 (inside : group⊆state.boulders) (bounded : group.length≤k)
 (holesInside : state.holes⊆soko1_1.initial.holes)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (avoid : ¬OwnedCorral11.PaidStep paid group dir t) :
 ∃j : Fin n, t.state.player∈region j ∧ locks j⊆update group outcome ∧
 update [marker i] outcome=[marker j] ∧ rank j≤rank i+gap state t group outcome := by
 have row := (groupCertificate k).row state dir t outcome group valid groupUnique inside bounded head effect
 have nonnegative : 0≤gap state t group outcome := by
   change value state group≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome) at row
   unfold gap
   omega
 have actualInside : locks i⊆state.boulders := List.Subset.trans locksInside inside
 have smallCorner := original_corner_projected soko1_1.board state (locks i) actualInside dir t head
 rcases step_cases_full soko1_1.board state dir t head with walked|pushed
 · obtain ⟨target,adjacent,floor,notBox,notHole,shape⟩ := walked
   have same := matches_unique state t (.walk target) outcome shape effect
   subst outcome
   have door := FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
   have notLock : target∉locks i := fun h => notBox (actualInside h)
   have nextHero := closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
   exact ⟨i,by simpa only [shape] using nextHero,locksInside,rfl,by omega⟩
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
   by_cases member : source∈locks i
   · have owner := locksInside member
     have unpaid : ¬paid source dir := by
       intro pays
       exact avoid ⟨source,owner,by simp only [shape],pays⟩
     have choice : BlockedPush soko1_1.board (locks i) source dir ∨
         Corral11.Shift soko1_1.board soko1_1.initial.holes locks region i source dir := by
       rcases closed.2 i state.player heroInside dir source member adjacent with blocked|paid|shift
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
       have rules := refined i state.player source dest dir j heroInside member adjacent first.1 unpaid destFloor targets noHole nextLocks nextHero
       have erased : (locks i).erase source⊆group.erase source := GhostSubset.erase_subset locksInside (unique i) source
       refine ⟨j,by simpa only [shape] using nextHero,?_,?_,?_⟩
       · simp only [update,move,if_pos owner,ending,notFilled,post]
         rw [landing]
         exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
       · simpa only [ending,notFilled,landing] using rules.1
       · rcases rules.2 with falls|⟨rises,exit⟩
         · omega
         · have priced := CutStrict11.exit_row scalar rfl valid head actualEffect groupUnique inside
             ⟨source,owner,by simp only [shape],exit⟩
           change 2≤gap state t group (.push source (ending result)) at priced
           omega
   · have noOwner : source∉group := by
       intro owner
       have all : source::locks i⊆group := by
         intro c found
         rcases List.mem_cons.mp found with rfl|later
         · exact owner
         · exact locksInside later
       have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
       simp only [List.length_cons,size i] at card
       omega
     have door := FiniteTopology.step_target_not_door _ _ _ _ _ adjacent head
     have nextHero := closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
     have noMarker : source∉[marker i] := by
       intro found
       have same : source=marker i := List.mem_singleton.mp found
       exact noOwner (same ▸ locksInside (markerInside i))
     refine ⟨i,by simpa only [shape] using nextHero,?_,?_,by omega⟩
     · simpa only [update,move,if_neg noOwner] using locksInside
     · simp only [update,move,if_neg noMarker]

theorem quiet_rank {n k : Nat} {locks region : Fin n→List Cell} {marker : Fin n→Cell}
 {rank : Fin n→Int} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (unique : ∀i, (locks i).Nodup) (size : ∀i, (locks i).length=k)
 (markerInside : ∀i, marker i∈locks i) (refined : Refinement locks region marker rank paid)
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤k)
 (i : Fin n) (heroInside : state.player∈region i) (locksInside : locks i⊆group)
 (holesInside : state.holes⊆soko1_1.initial.holes) :
 ∃j : Fin n, final.player∈region j ∧ locks j⊆endGroup group outcomes ∧
   endGroup [marker i] outcomes=[marker j] ∧ rank j≤rank i+energy state final group outcomes := by
 induction quiet generalizing i with
 | nil => exact ⟨i,heroInside,locksInside,rfl,by simp only [Hero315Frame11.energy,HeroLedger.energy,HeroLedger.charges,endGroup]; omega⟩
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   obtain ⟨j,nextHero,nextLocks,nextMarker,nextRank⟩ :=
     step_rank closed unique size markerInside refined valid groupUnique i heroInside locksInside inside bounded holesInside head effect avoid
   have nextValid := (groupCertificate k).preserved _ _ _ valid head
   have nextActual := step_boulders_nodup _ _ _ _ valid.1 head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group groupUnique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group groupUnique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   obtain ⟨last,lastHero,lastLocks,lastMarker,lastRank⟩ := ih nextValid nextUnique nextInside nextBound j nextHero nextLocks nextHoles
   have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
   change energy state final group (outcome::outcomes)=gap state t group outcome+energy t.state final (update group outcome) outcomes at decomposition
   refine ⟨last,lastHero,lastLocks,?_,?_⟩
   · simpa only [endGroup,nextMarker] using lastMarker
   · omega
#print axioms step_rank
#print axioms quiet_rank
end Owner1007.RankedCorral11
