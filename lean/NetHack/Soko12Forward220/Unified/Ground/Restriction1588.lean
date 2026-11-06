import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1588_0_checked : (List.range' 813056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1588_1_checked : (List.range' 813184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1588_2_checked : (List.range' 813312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1588_3_checked : (List.range' 813440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1588_range (index : Nat) (lower : 813056 ≤ index) (upper : index < 813568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 813312 then
    if cut : index < 813184 then
      exact segment_sound _ 813056 128 Restriction1588_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 813184 128 Restriction1588_1_checked index (by omega) (by omega)
  else
    if cut : index < 813440 then
      exact segment_sound _ 813312 128 Restriction1588_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 813440 128 Restriction1588_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
