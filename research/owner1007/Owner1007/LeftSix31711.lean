import Owner1007.LeftShaftPrice11
import Owner1007.LeftWestCount11
namespace Owner1007.LeftSix31711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem disjoint (source : Cell) (dir : Dir) :
 ¬(LeftPair11.paid source dir ∧Fixed317ShaftExit11.paid source dir) := by
 rintro ⟨⟨sources,rfl⟩,right⟩
 rcases sources with rfl|rfl|rfl|rfl <;> simpa [Fixed317ShaftExit11.paid] using right
theorem count_split (group : List Cell) (dirs : List Dir) (outcomes : List Outcome) :
 PaidCount11.count LeftShaftPrice11.paid group dirs outcomes=
 PaidCount11.count LeftPair11.paid group dirs outcomes+
 PaidCount11.count Fixed317ShaftExit11.paid group dirs outcomes := by
 induction dirs generalizing group outcomes with
 |nil=>simp [PaidCount11.count]
 |cons dir dirs ih=>
   cases outcomes with
   |nil=>simp [PaidCount11.count]
   |cons outcome outcomes=>
     have union : PaidCount11.owned LeftShaftPrice11.paid group dir outcome ↔
         PaidCount11.owned LeftPair11.paid group dir outcome ∨
         PaidCount11.owned Fixed317ShaftExit11.paid group dir outcome := by
       cases outcome <;> simp [PaidCount11.owned,LeftShaftPrice11.paid,and_or_left]
     have apart : ¬(PaidCount11.owned LeftPair11.paid group dir outcome ∧
         PaidCount11.owned Fixed317ShaftExit11.paid group dir outcome) := by
       cases outcome with
       |walk target=>simp [PaidCount11.owned]
       |push source ending=>exact fun both=>disjoint source dir ⟨both.1.2,both.2.2⟩
     have head : (if PaidCount11.owned LeftShaftPrice11.paid group dir outcome then 1 else 0)=
         (if PaidCount11.owned LeftPair11.paid group dir outcome then 1 else 0)+
         (if PaidCount11.owned Fixed317ShaftExit11.paid group dir outcome then 1 else 0) := by
       by_cases left : PaidCount11.owned LeftPair11.paid group dir outcome
       · by_cases right : PaidCount11.owned Fixed317ShaftExit11.paid group dir outcome
         · exact False.elim (apart ⟨left,right⟩)
         · rw [if_pos (union.mpr (Or.inl left)),if_pos left,if_neg right]
       · by_cases right : PaidCount11.owned Fixed317ShaftExit11.paid group dir outcome
         · rw [if_pos (union.mpr (Or.inr right)),if_neg left,if_pos right]
         · have neither : ¬PaidCount11.owned LeftShaftPrice11.paid group dir outcome :=
             fun h=>(union.mp h).elim left right
           rw [if_neg neither,if_neg left,if_neg right]
     simp only [PaidCount11.count,head,ih]
     omega
theorem consumed_six
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
   Fixed317Shaft11.locks Fixed317Shaft11.region Fixed317Shaft11.paid)
 (uniqueLocks : ∀i,(Fixed317Shaft11.locks i).Nodup)
 (sizeLocks : ∀i,(Fixed317Shaft11.locks i).length=2)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (stationary : ownPushes [317] outcomes=0) (consumed : endGroup [186,212] outcomes=[]) :
 6≤energy soko1_1.initial final [186,212] outcomes := by
 have west := LeftWestCount11.two logged consumed
 have subset := end_subset_selected logged (by decide) [212] [186,212] (by decide) (by decide) (by decide) (by decide)
 rw [consumed] at subset
 have gone : endGroup [212] outcomes=[] :=
   List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using subset member)
 have shaft := Fixed317ShaftExit11.nonwest_one closed uniqueLocks sizeLocks logged stationary gone
 have full := PaidCount11.energy_bound (paid:=LeftShaftPrice11.paid)
   (fun state dir t outcome group valid unique inside _ head effect pays=>
      LeftShaftPrice11.exit_row valid unique inside head effect pays)
   logged NetHack.SokobanLinearPhases.Map11.initial_good [186,212] (by decide) (by decide) (by decide)
 have sum := count_split [186,212] dirs outcomes
 simp only [Int.ofNat_eq_natCast] at full
 omega
theorem pair_six
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
   Fixed317Shaft11.locks Fixed317Shaft11.region Fixed317Shaft11.paid)
 (uniqueLocks : ∀i,(Fixed317Shaft11.locks i).Nodup)
 (sizeLocks : ∀i,(Fixed317Shaft11.locks i).length=2)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (stationary : ownPushes [317] outcomes=0) :
 6≤energy soko1_1.initial final [186,212] outcomes := by
 by_cases survives186 : endGroup [186] outcomes≠[]
 · have own := survivor_energy logged completed 186 survives186
   have debt : value soko1_1.initial [186]≤-6 := by decide +kernel
   have comparison := energy_subset (Trace.nil soko1_1.initial) logged [186] [186,212]
     (by decide) (by decide) (by decide) (by decide) (by decide)
   have nonnegative : (0:Int)≤Int.ofNat (ownPushes [186] outcomes) := Int.ofNat_nonneg _
   omega
 · by_cases survives212 : endGroup [212] outcomes≠[]
   · have own := survivor_energy logged completed 212 survives212
     have debt : value soko1_1.initial [212]≤-6 := by decide +kernel
     have comparison := energy_subset (Trace.nil soko1_1.initial) logged [212] [186,212]
       (by decide) (by decide) (by decide) (by decide) (by decide)
     have nonnegative : (0:Int)≤Int.ofNat (ownPushes [212] outcomes) := Int.ofNat_nonneg _
     omega
   · have gone186 : endGroup [186] outcomes=[] := Classical.byContradiction (fun h=>survives186 h)
     have gone212 : endGroup [212] outcomes=[] := Classical.byContradiction (fun h=>survives212 h)
     have perm := HeroLedger.Logged.end_append_perm logged (by decide) [186] [212] (by decide) (by decide)
     rw [gone186,gone212] at perm
     have gone : endGroup [186,212] outcomes=[] :=
       List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using perm.mem_iff.mp member)
     exact consumed_six closed uniqueLocks sizeLocks logged stationary gone
#print axioms pair_six
end Owner1007.LeftSix31711