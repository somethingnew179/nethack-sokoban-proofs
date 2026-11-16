import Owner1007.Post18712
import Owner1007.Quad211Trap12
namespace Owner1007.Post187Four12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem energy_four {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) {i : Fin 10}
    (hero : state.player ∈ Owner1007.Post18712.region i) (inside : Owner1007.Post18712.locks i ⊆ group) :
    4 ≤ energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ Post18712.matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed Owner1007.Post18712.unique logged reached group unique subset hero inside with event | terminal
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
    by_cases basic : j.val < 8
    · cases outcome with
      | walk target => exact False.elim pays
      | push source ending =>
        obtain ⟨owner,paid⟩ := pays
        obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
        let b : Fin 8 := ⟨j.val,basic⟩
        have same : Owner1007.Post18712.basic b = j := Fin.ext rfl
        have classified := Post18712.classification b middle.player (by simpa only [same] using heroBefore)
          dir source (Owner1007.Post18712.paid_sources source dir paid) adjacent paid
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
            (shift : small ⊆ dest :: (Owner1007.Post18712.locks j).erase source) :
            debtOf p small ≤ energy p (update (endGroup group before) (.push source ending)) after := by
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            targets clear checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Post18712.unique j) locks owner shift
          exact last.locked_group_energy Generated.soko1_2_potential_valid nextActual
            (update (endGroup group before) (.push source (.stay dest))) nextUnique nextSubset
            small locked smallUnique kept

        rcases classified with blocked | gateEvent | quadEvent | priceFour | priceTwo
        · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locks oldGroup.2) checked effect blocked)
        · obtain ⟨which,gateOrSquare⟩ := gateEvent
          have targets : pushTargets soko1_2.board source dir=[185] := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          have sourceRegion : source∈PriceTrap12Gate.region 0 := by
            rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
          rcases gateOrSquare with gate | square
          · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              targets (by decide +kernel) checked effect
            subst ending
            have kept := CageFour12.shifted_inside (Owner1007.Post18712.unique j) locks owner gate
            have newHero : t.state.player∈PriceTrap12Gate.region 0 := by
              rw [matches_hero middle t (.push source (.stay 185)) effect]
              exact sourceRegion
            have later := CageLedger12.gate_owned_nineteen last nextReached
              (update (endGroup group before) (.push source (.stay 185))) nextUnique nextSubset newHero kept
            change 19≤energy p (update (endGroup group before) (.push source (.stay 185))) after at later
            have bound := reserve 0 19 oneNN later
            omega
          · have later := lockedBound 185 targets (by decide +kernel)
              [158,159,184,185] (by decide +kernel) CageLedger12.locked_upper_square square
            have amount : (4:Int)≤debtOf p [158,159,184,185] := by decide +kernel
            have bound := reserve 0 (debtOf p [158,159,184,185]) oneNN later
            omega
        · obtain ⟨rfl,rfl,quad⟩ := quadEvent
          have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 212 .west=[211] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have kept := CageFour12.shifted_inside (Owner1007.Post18712.unique j) locks owner quad
          have newHero : t.state.player∈Quad211Trap12.region 0 := by
            rw [matches_hero middle t (.push 212 (.stay 211)) effect]
            decide +kernel
          have later := Quad211Trap12.owned_energy_fifteen last nextReached
            (update (endGroup group before) (.push 212 (.stay 211))) nextUnique nextSubset newHero kept
          change 15≤energy p (update (endGroup group before) (.push 212 (.stay 211))) after at later
          have bound := reserve 0 15 oneNN later
          omega
        · have one := push_effect_price p soko1_2.initial.holes 4 middleReached.holes_sublist.subset priceFour checked effect
          have bound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
          simp only [projectedOutcome,if_pos owner] at bound
          rw [shape]
          change slack p (.push source ending)≤energy p group (before++(.push source ending)::after) at bound
          omega
        · obtain ⟨notPair,priced⟩ := priceTwo
          have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
          have pairBefore : ([186,212] : List Cell)⊆endGroup group before :=
            List.Subset.trans (Owner1007.Post18712.pairInside j basic) locks
          have pairAfter := update_mono ([186,212] : List Cell) (endGroup group before)
            (by decide +kernel) pairBefore (.push source ending)
          simp only [update,move,if_neg notPair] at pairAfter
          have newHero : t.state.player∈VerticalPair12.region false 0 := by
            rw [matches_hero middle t (.push source ending) effect]
            exact Owner1007.Post18712.source_pair_outside source (Owner1007.Post18712.paid_sources source dir paid) notPair
          have later := VerticalPair12.owned_energy_two false last nextReached
            (update (endGroup group before) (.push source ending)) nextUnique nextSubset newHero pairAfter
          change 2≤energy p (update (endGroup group before) (.push source ending)) after at later
          exact reserve 2 2 one later
    · have large : 8 ≤ j.val := by omega
      have pair := Owner1007.Post18712.badPair j large
      have rest : Logged soko1_2.board middle (dir::afterDirs) final (t.pushCost+afterPushes) (1+afterMoves)
          (outcome::after) := .cons checked effect last
      rcases pair with pair | pair
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [210,236] CageLedger12.locked_210236 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [210,236] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (4 : Int) ≤ debtOf p [210,236] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
      · have later := rest.locked_group_energy Generated.soko1_2_potential_valid middleUnique
          (endGroup group before) oldGroup.1 oldGroup.2
          [184,210] CageLedger12.locked_184210 (by decide +kernel) (List.Subset.trans pair locks)
        change debtOf p [184,210] ≤ energy p (endGroup group before) (outcome::after) at later
        have amount : (4 : Int) ≤ debtOf p [184,210] := by decide +kernel
        rw [shape,TokenAccounting.energy_append]
        change 0 ≤ ownSlack p group before at prefixNN
        omega

  · obtain ⟨j,hero,locks⟩ := terminal
    have finalInside := logged.end_subset initialUnique group unique subset
    by_cases basic : j.val<8
    · have count := List.Nodup.length_le_of_subset (Owner1007.Post18712.unique j) (List.Subset.trans locks finalInside.2)
      have size : ∀ j : Fin 10, j.val<8 → 2<(Owner1007.Post18712.locks j).length := by decide +kernel
      have big := size j basic
      have conserved := (reached.append logged.trace).conservation
      have empty : final.holes=[] := completed
      change 20+final.holes.length=final.boulders.length+18 at conserved
      rw [empty] at conserved
      simp only [List.length_nil] at conserved
      omega
    · have large : 8≤j.val := by omega
      have pair := Owner1007.Post18712.badPair j large
      have nn := logged.ownSlack_nonnegative Generated.soko1_2_potential_valid group
      change 0≤ownSlack p group outcomes at nn
      have debtBound (small : List Cell) (smallUnique : small.Nodup) (kept : small⊆Owner1007.Post18712.locks j) :
          debtOf p small≤debtOf p (endGroup group outcomes) :=
        NonlinearFacts.weightSum_le_of_nodup_subset (fun c=>-p.boulder c)
          small (endGroup group outcomes)
          (fun c=> by have h:=Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c≤0 at h; omega)
          smallUnique (List.Subset.trans kept locks)
      rcases pair with pair | pair
      · have debt := debtBound [210,236] (by decide +kernel) pair
        have amount : (4:Int)≤debtOf p [210,236] := by decide +kernel
        unfold energy
        omega
      · have debt := debtBound [184,210] (by decide +kernel) pair
        have amount : (4:Int)≤debtOf p [184,210] := by decide +kernel
        unfold energy
        omega
#print axioms energy_four
end Owner1007.Post187Four12

