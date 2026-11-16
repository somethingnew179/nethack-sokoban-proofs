import Owner1007.Fixed317Shaft11Data
import Owner1007.PaidCount11
import Owner1007.QuietFixed11
import Owner1007.PairFirstCut11
import Owner1007.HeroEndSubset11
namespace Owner1007.Fixed317ShaftExit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=213 ∧dir=.east) ∨(source=291 ∧(dir=.east∨dir=.west∨dir=.south))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
theorem nonwest_one
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
   Fixed317Shaft11.locks Fixed317Shaft11.region Fixed317Shaft11.paid)
 (uniqueLocks : ∀i,(Fixed317Shaft11.locks i).Nodup)
 (sizeLocks : ∀i,(Fixed317Shaft11.locks i).length=2)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (stationary : ownPushes [317] outcomes=0) (consumed : endGroup [212] outcomes=[]) :
 1≤PaidCount11.count paid [186,212] dirs outcomes := by
 have good : OwnedCorral11.Good Fixed317Shaft11.locks Fixed317Shaft11.region soko1_1.initial [317,212] := by
   refine ⟨⟨3,by decide⟩,?_,?_⟩ <;> decide +kernel
 rcases first_cut_or_quiet (paid:=Fixed317Shaft11.paid) logged [317,212] with found|quiet
 · obtain ⟨cut⟩ := found
   have prefixZero := cut.before.fixed (by decide : 317∈([317,212] : List Cell))
     (fun dir=>by simp [Fixed317Shaft11.paid])
   have prefixTag : endGroup [317] cut.beforeOutcomes=[317] := no_push_unchanged _ _ prefixZero
   obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
   have nonstationary : source≠317 := by
     intro same;subst source
     have headOwn : ownPush [317] cut.headOutcome=1 := by
       cases h : cut.headOutcome with
       |walk target=>
         have effect := cut.headEffect
         rw [h] at effect
         rw [effect] at metadata
         contradiction
       |push other ending=>
         have effect := cut.headEffect
         rw [h] at effect
         have same : other=317 := by
           cases ending with
           |stay landing=>simpa only [effect.2,Option.some.injEq] using metadata
           |fill hole=>simpa only [effect.2.2,Option.some.injEq] using metadata
         subst other
         simp [ownPush]
     rw [cut.outcomesEq,ownPushes_append,prefixTag] at stationary
     simp only [ownPushes,headOwn] at stationary
     omega
   have exit : paid source cut.direction := by
     rcases pays with same|east|deep
     · exact False.elim (nonstationary same)
     · exact Or.inl east
     · exact Or.inr deep
   have beforePerm := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [317] [212] (by decide) (by decide)
   have original : source∈endGroup [212] cut.beforeOutcomes := by
     have member := beforePerm.mem_iff.mp owner
     rcases List.mem_append.mp member with first|second
     · rw [prefixTag] at first
       exact False.elim (nonstationary (List.mem_singleton.mp first))
     · exact second
   have inclusion := end_subset_selected cut.before.logged (by decide) [212] [186,212]
     (by decide) (by decide) (by decide) (by decide)
   have headPaid : OwnedCorral11.PaidStep paid (endGroup [186,212] cut.beforeOutcomes) cut.direction cut.actor :=
     ⟨source,inclusion original,metadata,exit⟩
   have bound := PaidCount11.event_le (paid:=paid) (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes)
     cut.before.logged cut.headEffect [186,212] headPaid
   rw [←cut.dirsEq,←cut.outcomesEq] at bound
   omega
 · obtain ⟨i,_,selected⟩ := PairFirstCut11.quiet_good closed uniqueLocks sizeLocks quiet
     (by decide) (by decide) (by decide) (by decide) good (by simp)
   have card := List.Nodup.length_le_of_subset (uniqueLocks i) selected
   have finalPerm := HeroLedger.Logged.end_append_perm logged (by decide) [317] [212] (by decide) (by decide)
   have tag : endGroup [317] outcomes=[317] := no_push_unchanged _ _ stationary
   rw [tag,consumed] at finalPerm
   have len : (endGroup [317,212] outcomes).length=1 := by
     simpa using finalPerm.length_eq
   rw [sizeLocks i] at card
   omega
#print axioms nonwest_one
end Owner1007.Fixed317ShaftExit11