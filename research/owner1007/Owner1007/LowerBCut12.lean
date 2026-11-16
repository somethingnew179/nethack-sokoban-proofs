import Owner1007.OwnedEventsMore12
import Owner1007.CageFour12
import Owner1007.TokenBounds32
import Owner1007.NorthEvents12
import Owner1007.Residual290Any12
import Owner1007.EndGroupMono
namespace Owner1007.LowerBCut12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def C : List Cell := [262,263,264,265]
def B (i : Fin 5) : List Cell := [318,NorthEvents12.current i]
def locks (i : Fin 5) : List Cell := C++B i
def region (i : Fin 5) : List Cell := NorthEvents12.region i++[210,236,237,238]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source∈C∧dir=.south)∨(source=318∧dir=.west)∨(source=291∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem large : ∀ i,(locks i).length=6 := by decide +kernel
def fixed : List Cell := C++[318]
theorem fixed_inside : ∀ i,fixed⊆locks i := by decide +kernel
theorem guard : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈fixed,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem price : ∀ source∈[262,263,264,265,318,291],∀ dir∈allDirs,paid source dir →
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧(if source=318 then (3:Int) else 2)≤1+p.boulder dest-p.boulder source := by decide +kernel
theorem hero : ∀ i,∀ cell∈([236,238]:List Cell),cell∈region i := by decide +kernel

theorem impossible {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final) (i : Fin 5)
 (hero0 : state.player∈region i) (inside : locks i⊆state.boulders)
 (coreZero : energy p C outcomes≤0)
 (bottomCheap : energy p (B i) outcomes≤2) :False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have exactSplit := logged.energy_split actualUnique p C (B i) (unique i) inside
 change energy p (locks i) outcomes=energy p C outcomes+energy p (B i) outcomes at exactSplit
 have jointCheap : energy p (locks i) outcomes≤2 := by omega
 rcases event_or_good closed unique logged reached (locks i) (unique i) inside hero0 (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroOne,locksOne,pays,fixedBefore⟩ :=
     event.split_fixed fixed fixed_inside
       (fun i hero h dir source m a=>guard i hero h dir (Geometry.all_directions dir) source m a)
       reached (unique i) inside
   have atReached := reached.append first.trace
   have atUnique := atReached.boulders_nodup (by decide +kernel)
   have old := first.end_subset actualUnique (locks i) (unique i) inside
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨owner,headPaid⟩:=pays
     have member : source∈([262,263,264,265,318,291]:List Cell) := by
       rcases headPaid with ⟨found,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
       · exact List.mem_append_left [318,291] found
       · decide +kernel
       · decide +kernel
     have rawPrice := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
       atReached.holes_sublist.subset (price source member dir (Geometry.all_directions dir) headPaid) checked effect
     rcases headPaid with ⟨core,south⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · have prior := fixedBefore C (by intro c h;exact List.mem_append_left _ h)
       have bound := event_energy_le Generated.soko1_2_potential_valid C first last (.push source ending)
       rw [prior] at bound
       simp only [projectedOutcome,if_pos core] at bound
       rw [←shape] at bound
       change slack p (.push source ending)≤energy p C outcomes at bound
       have not318 : source≠318 := by
         have all : ∀ c∈C,c≠318 := by decide +kernel
         exact all source core
       rw [if_neg not318] at rawPrice
       omega
     · have mono := first.end_mono actualUnique [318] (B i) (by decide +kernel)
         (List.Subset.trans ((show ∀ k,([318]:List Cell)⊆locks k from by decide +kernel) i) inside)
         (by simp [B])
       have prior := fixedBefore [318] (by decide +kernel)
       have ownBottom : (318:Cell)∈endGroup (B i) before := by
         apply mono
         rw [prior]
         simp
       have bound := event_energy_le Generated.soko1_2_potential_valid (B i) first last (.push 318 ending)
       simp only [projectedOutcome,if_pos ownBottom] at bound
       rw [←shape] at bound
       change slack p (.push 318 ending)≤energy p (B i) outcomes at bound
       have three : (3:Int)≤slack p (.push 318 ending) := by simpa using rawPrice
       omega
     · have sameEnding := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         NorthEvents12.ring_activation (by decide +kernel) checked effect
       subst ending
       have shift : ∀ j,Residual29012.locks 1⊆290::(locks j).erase 291 := by decide +kernel
       have kept := CageFour12.shifted_inside (unique j) locksOne owner (shift j)
       have nextActual := step_boulders_nodup _ _ _ _ atUnique checked
       have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
         (endGroup (locks i) before) old.1 old.2
       have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
         (endGroup (locks i) before) old.1 old.2
       have nextReached := atReached.append (Trace.cons checked (Trace.nil t.state))
       have nextHero : t.state.player∈Residual29012.region 1 := by
         rw [matches_hero middle t (.push 291 (.stay 290)) effect]
         decide +kernel
       have later := Residual290Any12.owned_energy_credit Residual29012.matrix last nextReached
         (update (endGroup (locks i) before) (.push 291 (.stay 290))) nextUnique nextSubset 1 nextHero kept
       change 3≤energy p (update (endGroup (locks i) before) (.push 291 (.stay 290))) after at later
       have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (locks i)
       change 0≤ownSlack p (locks i) before at prefixNN
       have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
       have whole := energy_at_split p (locks i) before (.push 291 (.stay 290)) after
       rw [←shape] at whole
       simp only [projectedOutcome,if_pos owner,one] at whole
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (locks i) (unique i) inside
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   rw [large j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms matrix
#print axioms impossible
end Owner1007.LowerBCut12
