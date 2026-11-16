import Owner1007.OwnedCorralAny11
import Owner1007.RankedCorral11
import Owner1007.OneWayToken11
namespace Owner1007.BudgetNoReturnBounded11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem no_return_quiet {n limit : Nat} {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (uniqueLocks : ∀i, (locks i).Nodup) (cell : Cell)
 (pricedLanding : ∀state dir t group source target,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤limit →
   OwnedCorral11.Good locks region state group →
   step soko1_1.board state dir=some t → Matches state t (.push source (.stay target)) →
   source∈group → target=cell →
   2≤RankedCorral11.gap state t group (.push source (.stay target)))
 {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤limit)
 (good : OwnedCorral11.Good locks region state group) (holesInside : state.holes⊆soko1_1.initial.holes)
 (cheap : energy state final group outcomes<2) :
 OneWayToken11.NoReturn cell group outcomes := by
 induction quiet with
 | nil => trivial
 | @cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih =>
   have nextValid := (groupCertificate limit).preserved _ _ _ valid head
   have nextActual := step_boulders_nodup _ _ _ _ valid.1 head
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group groupUnique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect group groupUnique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have tailNN := HeroLedger.Logged.energy_nonnegative tail.logged (groupCertificate limit) nextValid
     _ nextUnique nextInside nextBound
   change 0≤energy t.state final (update group outcome) outcomes at tailNN
   have row := (groupCertificate limit).row state dir t outcome group valid groupUnique inside bounded head effect
   change value state group≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome) at row
   have headNN : 0≤RankedCorral11.gap state t group outcome := by unfold RankedCorral11.gap; omega
   have decomposition := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
   change energy state final group (outcome::outcomes)=RankedCorral11.gap state t group outcome+energy t.state final (update group outcome) outcomes at decomposition
   have headCheap : RankedCorral11.gap state t group outcome<2 := by omega
   have tailCheap : energy t.state final (update group outcome) outcomes<2 := by omega
   have nextGood := OwnedCorralAny11.step_good_except closed uniqueLocks good inside holesInside head effect avoid
   have nextHoles := List.Subset.trans (step_holes_sublist _ _ _ _ head).subset holesInside
   have noLanding : OneWayToken11.AvoidLanding cell group outcome := by
     cases outcome with
     | walk _ => trivial
     | push source ending =>
       cases ending with
       | fill hole => trivial
       | stay target =>
         intro owner same
         have priced := pricedLanding state dir t group source target valid groupUnique inside bounded good head effect owner same
         omega
   exact ⟨noLanding,ih nextValid nextUnique nextInside nextBound nextGood nextHoles tailCheap⟩
#print axioms no_return_quiet
end Owner1007.BudgetNoReturnBounded11
