import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1559_0_checked : (List.range' 798208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1559_1_checked : (List.range' 798336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1559_2_checked : (List.range' 798464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1559_3_checked : (List.range' 798592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1559_range (index : Nat) (lower : 798208 ≤ index) (upper : index < 798720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 798464 then
    if cut : index < 798336 then
      exact segment_sound _ 798208 128 Restriction1559_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 798336 128 Restriction1559_1_checked index (by omega) (by omega)
  else
    if cut : index < 798592 then
      exact segment_sound _ 798464 128 Restriction1559_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 798592 128 Restriction1559_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
