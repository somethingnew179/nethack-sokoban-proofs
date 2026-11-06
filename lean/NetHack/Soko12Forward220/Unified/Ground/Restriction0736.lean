import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0736_0_checked : (List.range' 376832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0736_1_checked : (List.range' 376960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0736_2_checked : (List.range' 377088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0736_3_checked : (List.range' 377216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0736_range (index : Nat) (lower : 376832 ≤ index) (upper : index < 377344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 377088 then
    if cut : index < 376960 then
      exact segment_sound _ 376832 128 Restriction0736_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376960 128 Restriction0736_1_checked index (by omega) (by omega)
  else
    if cut : index < 377216 then
      exact segment_sound _ 377088 128 Restriction0736_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 377216 128 Restriction0736_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
