import Owner1007.TokenPersistence
import Owner1007.NorthEvents12
namespace Owner1007.SurvivorPrefix12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
theorem pushes_prefix_le (group : List Cell) (before after : List Outcome) :
    ownPushes group before≤ownPushes group (before++after) := by
  induction before generalizing group with
  | nil => simp only [ownPushes,List.nil_append]; omega
  | cons outcome rest ih =>
    simp only [List.cons_append,ownPushes]
    exact Nat.add_le_add_left (ih (update group outcome)) _

theorem survivor_energy_prefix_le (potential : Potential) (cell : Cell) (before after : List Outcome)
    (survivesBefore : endGroup [cell] before≠[])
    (survivesAll : endGroup [cell] (before++after)≠[]) :
    energy potential [cell] before≤energy potential [cell] (before++after) := by
  have earlier := survivor_energy potential cell before survivesBefore
  have later := survivor_energy potential cell (before++after) survivesAll
  have counts := pushes_prefix_le [cell] before after
  simp only [Int.ofNat_eq_natCast] at earlier later
  omega

theorem current_debt_for318 : ∀ i, ∀ hero∈NorthEvents12.region i,
    advance soko1_2.board hero .west=some 318 →
      4≤-p.boulder (NorthEvents12.current i) := by decide +kernel

theorem quantitative345 {state middle dirs pushes moves before}
    (first : Logged soko1_2.board state dirs middle pushes moves before)
    (after : List Outcome) (current : Cell)
    (prior : endGroup [345] before=[current])
    (debt : 4≤-p.boulder current)
    (survives : endGroup [345] (before++after)≠[]) :
    4≤energy p [345] (before++after) := by
  have pastNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [345]
  change 0≤ownSlack p [345] before at pastNN
  have pastEnergy : 4≤energy p [345] before := by
    unfold energy
    rw [prior]
    change 4≤ownSlack p [345] before + (-p.boulder current + 0)
    omega
  have nonempty : endGroup [345] before≠[] := by rw [prior]; simp
  exact Int.le_trans pastEnergy (survivor_energy_prefix_le p 345 before after nonempty survives)
#print axioms quantitative345
end Owner1007.SurvivorPrefix12

