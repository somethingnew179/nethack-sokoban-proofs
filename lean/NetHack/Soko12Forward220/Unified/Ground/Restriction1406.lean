import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1406_0_checked : (List.range' 719872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1406_1_checked : (List.range' 720000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1406_2_checked : (List.range' 720128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1406_3_checked : (List.range' 720256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1406_range (index : Nat) (lower : 719872 ≤ index) (upper : index < 720384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 720128 then
    if cut : index < 720000 then
      exact segment_sound _ 719872 128 Restriction1406_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 720000 128 Restriction1406_1_checked index (by omega) (by omega)
  else
    if cut : index < 720256 then
      exact segment_sound _ 720128 128 Restriction1406_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 720256 128 Restriction1406_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
