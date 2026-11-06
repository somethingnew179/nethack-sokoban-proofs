import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1642_0_checked : (List.range' 840704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1642_1_checked : (List.range' 840832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1642_2_checked : (List.range' 840960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1642_3_checked : (List.range' 841088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1642_range (index : Nat) (lower : 840704 ≤ index) (upper : index < 841216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 840960 then
    if cut : index < 840832 then
      exact segment_sound _ 840704 128 Restriction1642_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 840832 128 Restriction1642_1_checked index (by omega) (by omega)
  else
    if cut : index < 841088 then
      exact segment_sound _ 840960 128 Restriction1642_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 841088 128 Restriction1642_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
