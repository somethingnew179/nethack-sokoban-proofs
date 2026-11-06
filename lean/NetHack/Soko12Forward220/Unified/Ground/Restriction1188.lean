import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1188_0_checked : (List.range' 608256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1188_1_checked : (List.range' 608384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1188_2_checked : (List.range' 608512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1188_3_checked : (List.range' 608640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1188_range (index : Nat) (lower : 608256 ≤ index) (upper : index < 608768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 608512 then
    if cut : index < 608384 then
      exact segment_sound _ 608256 128 Restriction1188_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 608384 128 Restriction1188_1_checked index (by omega) (by omega)
  else
    if cut : index < 608640 then
      exact segment_sound _ 608512 128 Restriction1188_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 608640 128 Restriction1188_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
