import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1244_0_checked : (List.range' 636928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1244_1_checked : (List.range' 637056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1244_2_checked : (List.range' 637184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1244_3_checked : (List.range' 637312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1244_range (index : Nat) (lower : 636928 ≤ index) (upper : index < 637440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 637184 then
    if cut : index < 637056 then
      exact segment_sound _ 636928 128 Restriction1244_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 637056 128 Restriction1244_1_checked index (by omega) (by omega)
  else
    if cut : index < 637312 then
      exact segment_sound _ 637184 128 Restriction1244_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 637312 128 Restriction1244_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
