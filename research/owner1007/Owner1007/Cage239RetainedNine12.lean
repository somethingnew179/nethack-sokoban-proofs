import Owner1007.Cage239Retained12
namespace Owner1007.Cage239RetainedNine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.CageFour12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem energy_nine {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) {i : Fin 6}
    (hero : state.player ∈ Owner1007.Cage239RetainedNine12.region i) (inside : Owner1007.Cage239RetainedNine12.locks i ⊆ group) :
    9 ≤ energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed Owner1007.Cage239RetainedNine12.unique logged reached group unique subset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locks,pays⟩ := event.split
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldGroup := first.end_subset initialUnique group unique subset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
    by_cases basic : j.val < 4
    · cases outcome with
      | walk target => exact False.elim pays
      | push source ending =>
        obtain ⟨owner,paid⟩ := pays
        obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
        let b : Fin 4 := ⟨j.val,basic⟩
        have same : Owner1007.Cage239RetainedNine12.basic b = j := Fin.ext rfl
        have classified := classification b middle.player (by simpa only [same] using heroBefore)
          dir source (Owner1007.Cage239RetainedNine12.paid_sources source dir paid) adjacent paid
        rw [same] at classified
        have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
        have reserve (a b : Int) (one : a ≤ slack p (.push source ending))
            (later : b ≤ energy p (update (endGroup group before) (.push source ending)) after) :
            a+b ≤ energy p group outcomes := by
          rw [shape,energy_at_split]
          simp only [projectedOutcome,if_pos owner]
          change 0 ≤ ownSlack p group before at prefixNN
          omega
        have lockedBound (dest : Cell)
            (targets : pushTargets soko1_2.board source dir = [dest])
            (clear : dest ∉ soko1_2.initial.holes)
            (small : List Cell) (smallUnique : small.Nodup) (locked : Locked soko1_2.board small)
            (shift : small ⊆ dest :: (Owner1007.Cage239RetainedNine12.locks j).erase source) :
            debtOf p small ≤ energy p (update (endGroup group before) (.push source ending)) after := by
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            targets clear checked effect
          subst ending
          have kept := shifted_inside (Owner1007.Cage239RetainedNine12.unique j) locks owner shift
          exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
            (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
            small locked smallUnique kept
        rcases classified with blocked | upperEvent | gateEvent | squareEvent | priceTwo
        · exact False.elim (blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
        · obtain ⟨rfl,rfl⟩ := upperEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 213 .west=[212] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have kept := shifted_inside (Owner1007.Cage239RetainedNine12.unique j) locks owner (activation j basic)
          have newHero : t.state.player∈Cage21212.region (Cage212Nine12.normal (nextIndex j)) := by
            rw [matches_hero middle t (.push 213 (.stay 212)) effect]
            exact nextHero j basic
          have later := Cage212Nine12.energy_nine last nextReached
            (update (endGroup group before) (.push 213 (.stay 212))) nextUnique nextSubset completed (nextIndex j) newHero kept
          change 9≤energy p (update (endGroup group before) (.push 213 (.stay 212))) after at later
          have bound := reserve 0 9 oneNN later
          omega
        · obtain ⟨rfl,rfl,gateOrSquare⟩ := gateEvent
          rcases gateOrSquare with gate | square
          · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 211 .north = [185] by decide +kernel)
              (by decide +kernel) checked effect
            subst ending
            have kept := shifted_inside (Owner1007.Cage239RetainedNine12.unique j) locks owner gate
            have newHero : t.state.player ∈ PriceTrap12Gate.region 0 := by
              rw [matches_hero middle t (.push 211 (.stay 185)) effect]
              decide +kernel
            have later := CageLedger12.gate_owned_nineteen last nextReached
              (update (endGroup group before) (.push 211 (.stay 185))) nextUnique nextSubset newHero kept
            change 19 ≤ energy p (update (endGroup group before) (.push 211 (.stay 185))) after at later
            have bound := reserve 0 19 oneNN later
            omega
          · have later := lockedBound 185 (by decide +kernel) (by decide +kernel)
              [158,159,184,185] (by decide +kernel) CageLedger12.locked_upper_square square
            have amount : (9 : Int) ≤ debtOf p [158,159,184,185] := by decide +kernel
            have bound := reserve 0 (debtOf p [158,159,184,185]) oneNN later
            omega
        · obtain ⟨which,shifted⟩ := squareEvent
          have targets : pushTargets soko1_2.board source dir=[Owner1007.Cage23912.squareDest source] := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have clear : Owner1007.Cage23912.squareDest source∉soko1_2.initial.holes := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have later := lockedBound (Owner1007.Cage23912.squareDest source) targets clear
            [186,187,212,213] (by decide +kernel) CageLedger12.locked_middle_square shifted
          have amount : (9:Int)≤debtOf p [186,187,212,213] := by decide +kernel
          have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
          omega
        · obtain ⟨notUpper,priced⟩ := priceTwo
          have one := push_effect_price p soko1_2.initial.holes 7 middleReached.holes_sublist.subset priced checked effect
          have upperBefore : CageLedger12.Upper ⊆ endGroup group before :=
            List.Subset.trans (Owner1007.Cage239RetainedNine12.upperInside j) locks
          have upperAfter := update_mono CageLedger12.Upper (endGroup group before)
            (by decide +kernel) upperBefore (.push source ending)
          change source ∉ CageLedger12.Upper at notUpper
          simp only [update,move,if_neg notUpper] at upperAfter
          have actualUpper := List.Subset.trans upperAfter nextSubset
          have upperBound := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
            (by decide +kernel) actualUpper completed
          have allSources := Owner1007.Cage239RetainedNine12.paid_sources source dir paid
          have bonus : RightEnergy12.cert.bonus t.state.player
            (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
            rw [matches_hero middle t (.push source ending) effect]
            exact Owner1007.Cage239RetainedNine12.bonus source allSources notUpper
          rw [bonus] at upperBound
          change 2 ≤ energy p CageLedger12.Upper after at upperBound
          have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
            CageLedger12.Upper (update (endGroup group before) (.push source ending))
            (by decide +kernel) nextUnique actualUpper nextSubset upperAfter
          have later : (2 : Int) ≤ energy p (update (endGroup group before) (.push source ending)) after :=
            Int.le_trans upperBound mono
          exact reserve 7 2 one later
    · have large : 4 ≤ j.val := by omega
      have pair := Owner1007.Cage239RetainedNine12.pair j large
      have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
          (outcome::after) := .cons checked effect last
      rcases pair with pair | pair
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [210,236] CageLedger12.locked_210236 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [210,236] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (9 : Int) ≤ debtOf p [210,236] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [184,210] CageLedger12.locked_184210 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [184,210] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (9 : Int) ≤ debtOf p [184,210] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
  · obtain ⟨j,hero,locks⟩ := terminal
    have finalInside := logged.end_subset initialUnique group unique subset
    have count := List.Nodup.length_le_of_subset (Owner1007.Cage239RetainedNine12.unique j) (List.Subset.trans locks finalInside.2)
    have size : ∀ j, 2 < (Owner1007.Cage239RetainedNine12.locks j).length := by decide +kernel
    have big := size j
    have finalReached := reached.append logged.trace
    have conserved := finalReached.conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

#print axioms energy_nine
end Owner1007.Cage239RetainedNine12

