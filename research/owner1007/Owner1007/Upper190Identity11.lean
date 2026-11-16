import Owner1007.Upper190History11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.Upper190Identity11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11

theorem singleton_member (cells : List Cell) (cell : Cell) (bounded : cells.length≤1)
    (member : cell∈cells) : cells=[cell] := by
  cases cells with
  | nil => contradiction
  | cons first rest =>
    cases rest with
    | nil =>
      have same : cell=first := by simpa only [List.mem_singleton] using member
      exact congrArg (fun c => [c]) same.symm
    | cons next rest => simp only [List.length_cons] at bounded; omega

theorem original191_at190 {dirs state pushes moves outcomes}
    (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
    (still137 : ownPushes [137] outcomes=0) (still139 : ownPushes [139] outcomes=0)
    (selected190 : 190∈endGroup originalGroup outcomes) : endGroup [191] outcomes=[190] := by
  have one := HeroLedger.Logged.end_append_perm first (by decide) [137] [139,191] (by decide) (by decide)
  have two := HeroLedger.Logged.end_append_perm first (by decide) [139] [191] (by decide) (by decide)
  rw [no_push_unchanged _ _ still137] at one
  rw [no_push_unchanged _ _ still139] at two
  have combined : (endGroup originalGroup outcomes).Perm ([137,139] ++ endGroup [191] outcomes) :=
    one.trans ((List.Perm.refl [137]).append two)
  have member : 190∈endGroup [191] outcomes := by simpa using combined.mem_iff.mp selected190
  exact singleton_member _ 190 (Nat.le_trans (endGroup_length_le [191] outcomes) (by simp)) member

theorem separate188 {dirs state pushes moves outcomes}
    (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
    (cell : Cell) (inUpper : cell∈endGroup originalGroup outcomes) :
    cell∉endGroup [188] outcomes := by
  have selected := first.end_subset (by decide) (originalGroup++[188]) (by decide) (by decide)
  have split := HeroLedger.Logged.end_append_perm first (by decide) originalGroup [188] (by decide) (by decide)
  have unique := split.nodup_iff.mp selected.1
  intro in188
  exact (List.nodup_append.mp unique).2.2 cell inUpper cell in188 rfl

theorem FirstCut.original191_at190 {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west) :
    endGroup [191] cut.beforeOutcomes=[190] := by
  obtain ⟨still137,still139⟩ := Owner1007.Upper190History11.FirstCut.stationary_before_190west cut sourceEq directionEq
  obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
  have same : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
  exact Owner1007.Upper190Identity11.original191_at190 cut.before.logged still137 still139 (same ▸ owner)

#print axioms FirstCut.original191_at190
#print axioms separate188
end Owner1007.Upper190Identity11
