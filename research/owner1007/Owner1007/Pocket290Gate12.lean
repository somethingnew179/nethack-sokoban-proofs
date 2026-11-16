import Owner1007.FastCorral11
import Owner1007.OwnedEventsMore12
import Owner1007.CageLedger12
import Owner1007.AfterJ12
namespace Owner1007.Pocket290Gate12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def J : List Cell := [210,237,263,265,290]
def locks (_ : Fin 1) : List Cell := [210,211,213,237,263,265,290]
def region (_ : Fin 1) : List Cell := [29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,55,56,76,82,102,105,106,108,128,131,132,133,134,135,154,157,158,159,160,161,180,184,185,186,187,206,212,232,238,239,258,264,284,310,336]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=210∧dir=.south)∨(source=237∧dir=.west)∨(source=263∧dir=.west)∨
 (source=265∧dir=.south)∨(source=290∧dir=.west)∨
 (source=213∧(dir=.north∨dir=.south∨dir=.east))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem checked : ∀ i, FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes locks region paid i=true := by decide +kernel
theorem reverse : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem floors : ∀ i, region i⊆soko1_2.board.floor := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse floors checked
theorem unique : ∀ i,(locks i).Nodup := by decide +kernel
theorem fixed_inside : ∀ i,locks 0⊆locks i := by decide +kernel
theorem fixed_guard_check : ∀ i, ∀ hero∈region i, ∀ dir∈allDirs, ∀ source∈locks 0,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by decide +kernel
theorem fixed_guard : ∀ i hero, hero∈region i →∀ dir source, source∈locks 0 →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir∨paid source dir := by
 intro i hero h dir source m a
 exact fixed_guard_check i hero h dir (Geometry.all_directions dir) source m a
abbrev p := Generated.soko1_2Potential
theorem priced_check : ∀ source∈([210,237,263,265,290,213]:List Cell), ∀ dir∈allDirs,
 paid source dir →∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧(2:Int)≤1+p.boulder dest-p.boulder source := by decide +kernel
theorem paid_source {source dir} (h : paid source dir) : source=213∨source∈J := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
 all_goals simp[J]
theorem paid_all {source dir} (h : paid source dir) : source∈([210,237,263,265,290,213]:List Cell) := by
 rcases h with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
 all_goals decide +kernel
theorem heroes : ∀ c∈([264,187]:List Cell),c∈region 0 := by decide +kernel
theorem inaccessible : ∀ c∈([214,236,262,289,291]:List Cell),c∉region 0 := by decide +kernel
theorem after264_shift : ∀ j, locks 0⊆[211,213]++290::(AfterJ12.locks 1 j).erase 264 := by decide +kernel

theorem ordinary_two {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (completed : Goal final)
 (hero : state.player∈region 0) (subset : locks 0⊆state.boulders)
 (zero187 : energy p [213] outcomes=0) :
 2≤energy p J outcomes := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have nUnique : (locks 0).Nodup := unique 0
 rcases event_or_good closed unique logged reached (locks 0) nUnique subset hero (fun _ h=>h) with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,inside,pays,fixed⟩ :=
     event.split_fixed (locks 0) fixed_inside fixed_guard reached nUnique subset
   have middleReached := reached.append first.trace
   cases outcome with
   |walk target=>exact False.elim pays
   |push source ending=>
     obtain ⟨owner,paidHead⟩:=pays
     have price := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset
       (priced_check source (paid_all paidHead) dir (Geometry.all_directions dir) paidHead) checked effect
     rcases paid_source paidHead with rfl|member
     · have prior := fixed [213] (by decide +kernel)
       have bound := event_energy_le Generated.soko1_2_potential_valid [213] first last (.push 213 ending)
       rw[prior] at bound
       simp only[projectedOutcome,if_pos (show (213:Cell)∈([213]:List Cell) by decide +kernel)] at bound
       rw[←shape] at bound
       change slack p (.push 213 ending)≤energy p [213] outcomes at bound
       omega
     · have prior := fixed J (by decide +kernel)
       have bound := event_energy_le Generated.soko1_2_potential_valid J first last (.push source ending)
       rw[prior] at bound
       simp only[projectedOutcome,if_pos member] at bound
       rw[←shape] at bound
       change slack p (.push source ending)≤energy p J outcomes at bound
       omega
 · obtain ⟨j,_,kept⟩:=terminal
   have endInside := logged.end_subset actualUnique (locks 0) nUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans kept endInside.2)
   have size : ∀ j,(locks j).length=7 := by decide +kernel
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw[empty] at conserved
   simp only[List.length_nil] at conserved
   rw[size j] at count
   omega
#print axioms ordinary_two
end Owner1007.Pocket290Gate12
