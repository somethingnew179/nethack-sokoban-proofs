import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1948_0_checked : (List.range' 997376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1948_1_checked : (List.range' 997504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1948_2_checked : (List.range' 997632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1948_3_checked : (List.range' 997760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1948_range (index : Nat) (lower : 997376 ≤ index) (upper : index < 997888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 997632 then
    if cut : index < 997504 then
      exact segment_sound _ 997376 128 Restriction1948_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 997504 128 Restriction1948_1_checked index (by omega) (by omega)
  else
    if cut : index < 997760 then
      exact segment_sound _ 997632 128 Restriction1948_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 997760 128 Restriction1948_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
