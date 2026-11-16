import Owner1007.OwnedEventsMore12
import Owner1007.SidecarCriticalFixed12
namespace Owner1007.DiagonalDead26228912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks (_ : Fin 1) : List Cell := [262,289]
def region (_ : Fin 1) : List Cell := soko1_2.board.floor.filter fun c=>!([262,289,288]:List Cell).contains c
def paid (source : Cell) (dir : Dir) : Prop := (source=262∧dir=.south)∨(source=289∧dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem guard : ∀ i,∀ hero∈region i,∀ dir∈allDirs,∀ source∈locks 0,
 advance soko1_2.board hero dir=some source →BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem locked_low : Locked soko1_2.board [288,289] := locked_of_check _ _ (by decide +kernel)
theorem locked_high : Locked soko1_2.board [262,288] := locked_of_check _ _ (by decide +kernel)
theorem target_low : pushTargets soko1_2.board 262 .south=[288] := by decide +kernel
theorem target_high : pushTargets soko1_2.board 289 .west=[288] := by decide +kernel

theorem preserved_length {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders) :
 (endGroup (locks 0) outcomes).length=2 := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have short := endGroup_length_le (locks 0) outcomes
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 rcases event_or_good closed unique logged reached (locks 0) (unique 0) inside hero (fun _ h=>h) with event|terminal
 · obtain ⟨bd,bp,bm,before,middle,dir,t,outcome,after,ad,ap,am,j,shape,first,checked,effect,last,heroHead,locksHead,pays,fixed⟩ :=
     event.split_fixed (locks 0) (fun _=>fun _ h=>h)
       (fun i hero h dir source m a=>guard i hero h dir (Geometry.all_directions dir) source m a)
       reached (unique 0) inside
   have prior := fixed (locks 0) (fun _ h=>h)
   have middleInside := first.end_subset actualUnique (locks 0) (unique 0) inside
   rw [prior] at middleInside
   have atReached := reached.append first.trace
   have nextActual := step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) checked
   have nextSubset := GhostSubset.update_subset middle t outcome effect (locks 0) (unique 0) middleInside.2
   cases outcome with
   | walk target=>exact False.elim pays
   | push source ending=>
     obtain ⟨_,headPaid⟩:=pays
     rcases headPaid with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         target_low (by decide +kernel) checked effect
       subst ending
       have nextPair : update (locks 0) (.push 262 (.stay 288))=[288,289] := by decide +kernel
       rw [nextPair] at nextSubset
       have kept := last.locked_end_inside nextActual [288,289] (by decide +kernel) nextSubset
         [288,289] locked_low (fun _ h=>h)
       have count := List.Nodup.length_le_of_subset (by decide +kernel : ([288,289]:List Cell).Nodup) kept
       rw [shape,endGroup_append,prior]
       change (endGroup (update (locks 0) (.push 262 (.stay 288))) after).length=2
       rw [nextPair]
       have short' := endGroup_length_le [288,289] after
       simp only [List.length_cons,List.length_nil] at count short'
       omega
     · have same := push_effect_singleton soko1_2.initial.holes atReached.holes_sublist.subset
         target_high (by decide +kernel) checked effect
       subst ending
       have nextPair : update (locks 0) (.push 289 (.stay 288))=[288,262] := by decide +kernel
       rw [nextPair] at nextSubset
       have kept := last.locked_end_inside nextActual [288,262] (by decide +kernel) nextSubset
         [262,288] locked_high (by decide +kernel)
       have count := List.Nodup.length_le_of_subset (by decide +kernel : ([262,288]:List Cell).Nodup) kept
       rw [shape,endGroup_append,prior]
       change (endGroup (update (locks 0) (.push 289 (.stay 288))) after).length=2
       rw [nextPair]
       have short' := endGroup_length_le [288,262] after
       simp only [List.length_cons,List.length_nil] at count short'
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have count := List.Nodup.length_le_of_subset (unique j) kept
   have size : ∀ i,(locks i).length=2 := by decide +kernel
   rw [size j] at count
   rw [size 0] at short
   omega

theorem energy_ten {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (hero : state.player∈region 0) (inside : locks 0⊆state.boulders) :
 10≤energy p (locks 0) outcomes := by
 have length := preserved_length logged reached hero inside
 have credits := SidecarCriticalFixed12.credits_zero_of_preserved_length p (locks 0) outcomes (by simpa [locks] using length)
 have ledger := group_ledger p (locks 0) outcomes
 have debt : debtOf p (locks 0)=10 := by decide +kernel
 rw [credits,debt] at ledger
 have pushesNN : (0:Int)≤Int.ofNat (ownPushes (locks 0) outcomes) := Int.ofNat_nonneg _
 change 10+Int.ofNat (ownPushes (locks 0) outcomes)=energy p (locks 0) outcomes+0 at ledger
 omega
#print axioms matrix
#print axioms preserved_length
#print axioms energy_ten
end Owner1007.DiagonalDead26228912
