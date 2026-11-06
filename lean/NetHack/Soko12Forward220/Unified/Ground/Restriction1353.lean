import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1353_0_checked : (List.range' 692736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1353_1_checked : (List.range' 692864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1353_2_checked : (List.range' 692992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1353_3_checked : (List.range' 693120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1353_range (index : Nat) (lower : 692736 ≤ index) (upper : index < 693248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 692992 then
    if cut : index < 692864 then
      exact segment_sound _ 692736 128 Restriction1353_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 692864 128 Restriction1353_1_checked index (by omega) (by omega)
  else
    if cut : index < 693120 then
      exact segment_sound _ 692992 128 Restriction1353_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 693120 128 Restriction1353_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
