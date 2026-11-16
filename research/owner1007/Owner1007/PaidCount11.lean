import Owner1007.UpperFirstCut11
import Owner1007.Hero315Frame11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.PaidCount11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def owned (paid : Cell→Dir→Prop) (group : List Cell) (dir : Dir) : Outcome→Prop
 |.walk _=>False
 |.push source _=>source∈group∧paid source dir
instance (paid : Cell→Dir→Prop) [∀c d,Decidable (paid c d)] (group : List Cell) (dir : Dir) (outcome : Outcome) :
 Decidable (owned paid group dir outcome) := by cases outcome <;> unfold owned <;> infer_instance
def count (paid : Cell→Dir→Prop) [∀c d,Decidable (paid c d)] : List Cell→List Dir→List Outcome→Nat
 |group,dir::dirs,outcome::outcomes=>(if owned paid group dir outcome then 1 else 0)+count paid (update group outcome) dirs outcomes
 |_,_,_=>0
theorem owned_iff {paid group dir state t outcome}
 (effect : Matches state t outcome) :
 owned paid group dir outcome ↔ OwnedCorral11.PaidStep paid group dir t := by
 cases outcome with
 |walk target=>
   constructor
   · intro h;contradiction
   · rintro ⟨source,owner,metadata,pays⟩
     rw [effect] at metadata
     contradiction
 |push source ending=>
   constructor
   · intro h
     refine ⟨source,h.1,?_,h.2⟩
     cases ending with
     |stay landing=>rw [effect.2]
     |fill hole=>rw [effect.2.2]
   · rintro ⟨other,owner,metadata,pays⟩
     have same : other=source := by
       cases ending with
       |stay landing=>simpa only [effect.2,Option.some.injEq] using metadata.symm
       |fill hole=>simpa only [effect.2.2,Option.some.injEq] using metadata.symm
     subst other
     exact ⟨owner,pays⟩
theorem append {board state dirs final pushes moves outcomes}
 (logged : Logged board state dirs final pushes moves outcomes)
 (paid : Cell→Dir→Prop) [∀c d,Decidable (paid c d)]
 (group : List Cell) (lastDirs : List Dir) (lastOutcomes : List Outcome) :
 count paid group (dirs++lastDirs) (outcomes++lastOutcomes)=
 count paid group dirs outcomes + count paid (endGroup group outcomes) lastDirs lastOutcomes := by
 induction logged generalizing group with
 |nil=>simp [count,endGroup]
 |cons head effect tail ih=> simp only [List.cons_append,count,endGroup,ih,Nat.add_assoc]
theorem event_le {paid} [∀c d,Decidable (paid c d)]
 {state middle t beforeDirs beforePushes beforeMoves before dir outcome lastDirs last}
 (first : Logged soko1_1.board state beforeDirs middle beforePushes beforeMoves before)
 (effect : Matches middle t outcome) (group : List Cell)
 (pays : OwnedCorral11.PaidStep paid (endGroup group before) dir t) :
 1+count paid (update (endGroup group before) outcome) lastDirs last ≤
 count paid group (beforeDirs++dir::lastDirs) (before++outcome::last) := by
 rw [append first]
 have owner := (owned_iff effect).mpr pays
 simp only [count,if_pos owner]
 omega
theorem energy_bound {paid} [∀c d,Decidable (paid c d)]
 (priced : ∀state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup →group⊆state.boulders →group.length≤18 →
   step soko1_1.board state dir=some t →Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group)
 {state dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18) :
 2*Int.ofNat (count paid group dirs outcomes)≤energy state final group outcomes := by
 induction logged generalizing group with
 |nil=>simp [count,Hero315Frame11.energy,HeroLedger.energy,HeroLedger.charges,endGroup]
 |@cons state dir t rest final pushes moves outcome outcomes head effect tail ih=>
   have nextValid := (groupCertificate 18).preserved _ _ _ valid head
   have actual := step_boulders_nodup _ _ _ _ valid.1 head
   have nextUnique := GhostSubset.update_unique _ _ _ effect actual _ unique inside
   have nextInside := GhostSubset.update_subset _ _ _ effect _ unique inside
   have nextBound := Nat.le_trans (update_length group outcome) bounded
   have later := ih nextValid (update group outcome) nextUnique nextInside nextBound
   simp only [Int.ofNat_eq_natCast] at later
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final group outcome outcomes
   change energy state final group (outcome::outcomes)=
     charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome)-value state group+
     energy t.state final (update group outcome) outcomes at one
   by_cases pays : owned paid group dir outcome
   · have row := priced state dir t outcome group valid unique inside bounded head effect ((owned_iff effect).mp pays)
     simp only [count,if_pos pays,Int.ofNat_eq_natCast,Int.natCast_add]
     omega
   · have row := (groupCertificate 18).row state dir t outcome group valid unique inside bounded head effect
     change value state group≤charge NetHack.Soko11Hero315.holeWeight group outcome+value t.state (update group outcome) at row
     simp only [count,if_neg pays,Nat.zero_add,Int.ofNat_eq_natCast]
     omega
#print axioms energy_bound
end Owner1007.PaidCount11