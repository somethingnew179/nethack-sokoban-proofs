import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0895_0_checked : (List.range' 458240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0895_1_checked : (List.range' 458368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0895_2_checked : (List.range' 458496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0895_3_checked : (List.range' 458624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0895_range (index : Nat) (lower : 458240 ≤ index) (upper : index < 458752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 458496 then
    if cut : index < 458368 then
      exact segment_sound _ 458240 128 Restriction0895_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 458368 128 Restriction0895_1_checked index (by omega) (by omega)
  else
    if cut : index < 458624 then
      exact segment_sound _ 458496 128 Restriction0895_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 458624 128 Restriction0895_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
