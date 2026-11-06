import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1604_0_checked : (List.range' 821248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1604_1_checked : (List.range' 821376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1604_2_checked : (List.range' 821504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1604_3_checked : (List.range' 821632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1604_range (index : Nat) (lower : 821248 ≤ index) (upper : index < 821760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 821504 then
    if cut : index < 821376 then
      exact segment_sound _ 821248 128 Restriction1604_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 821376 128 Restriction1604_1_checked index (by omega) (by omega)
  else
    if cut : index < 821632 then
      exact segment_sound _ 821504 128 Restriction1604_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 821632 128 Restriction1604_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
