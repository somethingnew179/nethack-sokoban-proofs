import Owner1007.PairFirstCut11
import Owner1007.UpperHeadCases11
import Owner1007.PostEnergy11
namespace Owner1007.PairPost11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.LowerBounds
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.PairFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def edges : List (Cell×Cell×Cell×Dir×List Cell×List Cell) :=
 [(137,138,139,.east,[138,191],[139,191]),(139,138,137,.west,[138,191],[137,191]),
  (189,190,191,.east,[139,190],[139,191]),(191,190,189,.west,[139,190],[139,189]),
  (111,112,113,.east,[139,112],[139,113]),(215,216,217,.east,[216,191],[191,217])]
def Spec (support source landing : Cell) (dir : Dir) (old next : List Cell) : Prop :=
 ActorPrices11.supportCheck source support dir=true ∧ advance soko1_1.board source dir=some landing ∧
 ∀ i : Fin 9, source∈PairPath11.locks i → support∈PairPath11.region i → landing∉PairPath11.locks i →
   (PairPath11.locks i).Perm old ∧ (update (PairPath11.locks i) (.push source (.stay landing))).Perm next
instance (support source landing : Cell) (dir : Dir) (old next : List Cell) : Decidable (Spec support source landing dir old next) := by
 unfold Spec
 infer_instance
theorem checked : edges.all (fun (support,source,landing,dir,old,next) => decide (Spec support source landing dir old next))=true := by decide +kernel

theorem canonical_group (i : Fin 9) (group : List Cell) (unique : group.Nodup) (bounded : group.length≤2)
 (inside : PairPath11.locks i⊆group) : group.Perm (PairPath11.locks i) := by
 apply (List.perm_ext_iff_of_nodup unique (PairPath11.unique i)).mpr
 intro cell
 constructor
 · intro member
   by_cases known : cell∈PairPath11.locks i
   · exact known
   · have all : cell::PairPath11.locks i⊆group := by
       intro c found
       rcases List.mem_cons.mp found with rfl|later
       · exact member
       · exact inside later
     have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨known,PairPath11.unique i⟩) all
     simp only [List.length_cons,PairPath11.size i] at card
     omega
 · exact fun h => inside h

theorem source_adjacent {state : State} {t : Transition} {source : Cell} {dir : Dir}
 (checked : step soko1_1.board state dir=some t) (sourceEq : t.pushSource=some source) :
 advance soko1_1.board state.player dir=some source := by
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 · obtain ⟨target,_,_,_,_,shape⟩ := walked
   simp only [shape] at sourceEq
   contradiction
 · obtain ⟨other,result,adjacent,_,_,_,shape⟩ := pushed
   have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
   simpa only [same] using adjacent

theorem before_after {dirs final pushes moves outcomes} {support source landing : Cell} {dir : Dir} {old next : List Cell}
 (cut : UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (member : (support,source,landing,dir,old,next)∈edges)
 (sourceEq : cut.actor.pushSource=some source) (directionEq : cut.direction=dir)
 (effect : Matches cut.middle cut.actor (.push source (.stay landing))) :
 (endGroup originalGroup cut.beforeOutcomes).Perm old ∧
 (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome).Perm next := by
 have spec := of_decide_eq_true (List.all_eq_true.mp checked _ member)
 have checked : step soko1_1.board cut.middle dir=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have hero := ActorPrices11.support_of_check source cut.middle.player dir support spec.1
   (step_player_clear _ _ _ _ checked).1 (source_adjacent checked sourceEq)
 have noLanding : landing∉cut.middle.boulders := by
   obtain ⟨result,_,push⟩ := effect_push_data checked effect
   obtain ⟨dest,next,_,_,empty⟩ := (push_first_clear _ _ _ _ _ push).2
   have same : dest=landing := Option.some.inj (next.symm.trans spec.2.1)
   exact same ▸ empty
 have good := quiet_good PairPath11.closed PairPath11.unique PairPath11.size cut.before
   (by decide) (by decide) (by decide) (by decide) initial_good (by simp)
 obtain ⟨i,heroInside,locksInside⟩ := good
 have selected := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
 have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
 have canonical := canonical_group i _ selected.1 bounded locksInside
 obtain ⟨other,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : other=source := Option.some.inj (metadata.symm.trans sourceEq)
 have sourceOwn : source∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have sourceLock := lock_complete i _ bounded locksInside source sourceOwn
 have heroIn : support∈PairPath11.region i := by simpa only [hero] using heroInside
 have landingOut : landing∉PairPath11.locks i := fun found => noLanding (selected.2 (locksInside found))
 have rows := spec.2.2 i sourceLock heroIn landingOut
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome
   (.push source (.stay landing)) cut.headEffect effect
 refine ⟨canonical.trans rows.1,?_⟩
 have after := update_perm canonical cut.headOutcome
 rw [headEq] at after
 rw [headEq]
 exact after.trans rows.2
#print axioms before_after
end Owner1007.PairPost11
