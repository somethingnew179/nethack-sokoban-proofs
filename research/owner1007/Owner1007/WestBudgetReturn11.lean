import Owner1007.WestRankHead11
import Owner1007.OneWayToken11
import Owner1007.PairFirstCut11
namespace Owner1007.WestBudgetReturn11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def landingCheck : Bool := ([136,139] : List Cell).all fun cell => (List.finRange 15).all fun i =>
 (WestRank11.locks i).all fun source => allDirs.all fun dir =>
 (pushTargets soko1_1.board source dir).all fun target =>
 decide (dir.diagonal=false → target=cell → CutActor11.Exit source dir)
theorem landing_checked : landingCheck=true := by decide +kernel
theorem exit_of_landing (cell : Cell) (member : cell∈[136,139]) (i : Fin 15) (source target : Cell) (dir : Dir)
 (sourceInside : source∈WestRank11.locks i) (cardinal : dir.diagonal=false)
 (landing : target∈pushTargets soko1_1.board source dir) (same : target=cell) : CutActor11.Exit source dir := by
 have a := List.all_eq_true.mp landing_checked cell member
 have b := List.all_eq_true.mp (List.all_eq_true.mp a i (by simp)) source sourceInside
 have c := List.all_eq_true.mp b dir (Geometry.all_directions dir)
 exact of_decide_eq_true (List.all_eq_true.mp c target landing) cardinal same

theorem paid_row {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good WestRank11.locks WestRank11.region state group)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (pays : OwnedCorral11.PaidStep WestRank11.paid group dir t) :
 2≤RankedCorral11.gap state t group outcome := by
 obtain ⟨i,heroInside,locksInside⟩ := good
 obtain ⟨source,owner,metadata,shape⟩ := WestRankHead11.head_shape i heroInside locksInside inside bounded head pays
 rcases shape with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
 · exact WestRankHead11.row136 valid head effect metadata owner unique inside
 · exact CutStrict11.exit_row scalar rfl valid head effect unique inside ⟨139,owner,metadata,by simp [CutActor11.Exit]⟩
 · exact CutStrict11.exit_row scalar rfl valid head effect unique inside ⟨191,owner,metadata,by simp [CutActor11.Exit]⟩
 · exact CutStrict11.exit_row scalar rfl valid head effect unique inside ⟨216,owner,metadata,by simp [CutActor11.Exit]⟩

theorem no_return {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good WestRank11.locks WestRank11.region state group)
 (cheap : energy state final group outcomes<2) (cell : Cell) (member : cell∈[136,139]) :
 OneWayToken11.NoReturn cell group outcomes := by
 induction logged generalizing group history beforePushes beforeMoves with
 | nil => trivial
 | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have nextValid := (groupCertificate 3).preserved _ _ _ valid head
   have nextActual := step_boulders_nodup _ _ _ _ valid.1 head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group unique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have tailNN := HeroLedger.Logged.energy_nonnegative tail (groupCertificate 3) nextValid
     _ nextUnique nextInside nextBound
   change 0≤energy t.state final (update group outcome) outcomes at tailNN
   have row := (groupCertificate 3).row state dir t outcome group valid unique inside bounded head effect
   change value state group≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome) at row
   have headNN : 0≤RankedCorral11.gap state t group outcome := by unfold RankedCorral11.gap; omega
   have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
   change energy state final group (outcome::outcomes)=RankedCorral11.gap state t group outcome+energy t.state final (update group outcome) outcomes at decomposition
   have headCheap : RankedCorral11.gap state t group outcome<2 := by omega
   have tailCheap : energy t.state final (update group outcome) outcomes<2 := by omega
   have avoid : ¬OwnedCorral11.PaidStep WestRank11.paid group dir t := by
     intro pays
     have priced := paid_row valid unique inside bounded good head effect pays
     omega
   have nextGood := OwnedCorral11.step_good_except WestRank11.closed WestRank11.unique WestRank11.size good inside bounded
     reached.holes_sublist.subset head effect avoid
   have noLanding : OneWayToken11.AvoidLanding cell group outcome := by
     cases outcome with
     | walk _ => trivial
     | push source ending =>
       cases ending with
       | fill hole => trivial
       | stay target =>
         intro owner same
         obtain ⟨i,heroInside,locksInside⟩ := good
         have sourceInside := WestRankHead11.lock_complete i group bounded locksInside source owner
         obtain ⟨cardinal,landing⟩ := UpperQuiet11.stay_geometry head effect
         have exit := exit_of_landing cell member i source target dir sourceInside cardinal landing same
         have priced := CutStrict11.exit_row scalar rfl valid head effect unique inside
           ⟨source,owner,by rw [effect.2],exit⟩
         change 2≤RankedCorral11.gap state t group (.push source (.stay target)) at priced
         omega
   have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
   exact ⟨noLanding,ih (history:=history++[dir]) (beforePushes:=beforePushes+(t.pushCost+0)) (beforeMoves:=beforeMoves+(1+0)) nextReached (update group outcome) nextUnique nextInside nextBound nextGood tailCheap⟩
#print axioms no_return
end Owner1007.WestBudgetReturn11
