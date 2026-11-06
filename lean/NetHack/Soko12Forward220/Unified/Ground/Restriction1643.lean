import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1643_0_checked : (List.range' 841216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1643_1_checked : (List.range' 841344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1643_2_checked : (List.range' 841472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1643_3_checked : (List.range' 841600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1643_range (index : Nat) (lower : 841216 ≤ index) (upper : index < 841728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 841472 then
    if cut : index < 841344 then
      exact segment_sound _ 841216 128 Restriction1643_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 841344 128 Restriction1643_1_checked index (by omega) (by omega)
  else
    if cut : index < 841600 then
      exact segment_sound _ 841472 128 Restriction1643_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 841600 128 Restriction1643_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
