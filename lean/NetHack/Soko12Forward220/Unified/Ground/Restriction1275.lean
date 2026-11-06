import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1275_0_checked : (List.range' 652800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1275_1_checked : (List.range' 652928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1275_2_checked : (List.range' 653056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1275_3_checked : (List.range' 653184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1275_range (index : Nat) (lower : 652800 ≤ index) (upper : index < 653312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 653056 then
    if cut : index < 652928 then
      exact segment_sound _ 652800 128 Restriction1275_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 652928 128 Restriction1275_1_checked index (by omega) (by omega)
  else
    if cut : index < 653184 then
      exact segment_sound _ 653056 128 Restriction1275_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 653184 128 Restriction1275_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
