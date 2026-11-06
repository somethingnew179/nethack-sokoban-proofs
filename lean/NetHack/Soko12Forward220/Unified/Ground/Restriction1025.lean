import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1025_0_checked : (List.range' 524800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1025_1_checked : (List.range' 524928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1025_2_checked : (List.range' 525056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1025_3_checked : (List.range' 525184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1025_range (index : Nat) (lower : 524800 ≤ index) (upper : index < 525312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 525056 then
    if cut : index < 524928 then
      exact segment_sound _ 524800 128 Restriction1025_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 524928 128 Restriction1025_1_checked index (by omega) (by omega)
  else
    if cut : index < 525184 then
      exact segment_sound _ 525056 128 Restriction1025_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 525184 128 Restriction1025_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
