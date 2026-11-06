import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1295_0_checked : (List.range' 663040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1295_1_checked : (List.range' 663168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1295_2_checked : (List.range' 663296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1295_3_checked : (List.range' 663424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1295_range (index : Nat) (lower : 663040 ≤ index) (upper : index < 663552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 663296 then
    if cut : index < 663168 then
      exact segment_sound _ 663040 128 Restriction1295_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 663168 128 Restriction1295_1_checked index (by omega) (by omega)
  else
    if cut : index < 663424 then
      exact segment_sound _ 663296 128 Restriction1295_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 663424 128 Restriction1295_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
