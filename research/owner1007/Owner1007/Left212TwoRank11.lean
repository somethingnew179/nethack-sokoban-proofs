import Owner1007.Left212TwoWord11
namespace Owner1007.Left212TwoWord11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guard_rank_aux {state final : State} {group : List Cell} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet early state group dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (cell : Cell) (tagEq : group=[cell]) (member : cell∈cells) (present : cell∈state.boulders)
 (cheap : energy state final group outcomes<4-rank cell) :
 ∃dest,dest∈cells ∧endGroup group outcomes=[dest] ∧rank dest≤rank cell+energy state final group outcomes := by
 induction quiet generalizing cell with
 |nil=>
  cases tagEq
  refine ⟨cell,member,rfl,?_⟩
  simp [Owner1007.Hero315Frame11.energy,HeroLedger.energy,HeroLedger.charges,endGroup]
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
  cases tagEq
  have nextValid:=(groupCertificate 1).preserved _ _ _ valid head
  have actual:=step_boulders_nodup _ _ _ _ valid.1 head
  have inside : [cell]⊆state.boulders := by simpa using present
  have selectedUnique:=GhostSubset.update_unique _ _ _ effect actual [cell] (by simp) inside
  have selectedInside:=GhostSubset.update_subset _ _ _ effect [cell] (by simp) inside
  have selectedBound : (update [cell] outcome).length≤1 := Nat.le_trans (update_length _ _) (by simp)
  have tailNN:=HeroLedger.Logged.energy_nonnegative tail.logged (groupCertificate 1) nextValid
    (update [cell] outcome) selectedUnique selectedInside selectedBound
  change 0≤energy t.state final (update [cell] outcome) outcomes at tailNN
  have certrow:=(groupCertificate 1).row state dir t outcome [cell] valid (by simp) inside (by simp) head effect
  change value state [cell]≤charge NetHack.Soko11Hero315.holeWeight [cell] outcome+value t.state (update [cell] outcome) at certrow
  have rowNN : 0≤row state t cell outcome := by unfold row;omega
  have split:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final [cell] outcome outcomes
  change energy state final [cell] (outcome::outcomes)=row state t cell outcome+
    energy t.state final (update [cell] outcome) outcomes at split
  have firstCheap : row state t cell outcome<4-rank cell := by omega
  obtain ⟨dest,destMember,updated,rankBound⟩:=one_step valid member present head effect avoid firstCheap
  have nextPresent : dest∈t.state.boulders := selectedInside (by rw [updated];simp)
  have nextCheap : energy t.state final (update [cell] outcome) outcomes<4-rank dest := by omega
  obtain ⟨last,lastMember,lastTag,lastRank⟩:=ih nextValid dest updated destMember nextPresent nextCheap
  exact ⟨last,lastMember,lastTag,by omega⟩


theorem guard_rank {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (quiet : UpperQuiet11.Quiet early state [212] dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (present : 212∈state.boulders) (cheap : energy state final [212] outcomes<4) :
 ∃dest,dest∈cells ∧endGroup [212] outcomes=[dest] ∧rank dest≤energy state final [212] outcomes := by
 have startRank : rank 212=0 := by decide +kernel
 obtain ⟨dest,member,tag,bound⟩:=guard_rank_aux quiet valid 212 rfl (by decide) present (by rw [startRank];omega)
 exact ⟨dest,member,tag,by omega⟩
#print axioms guard_rank
end Owner1007.Left212TwoWord11
