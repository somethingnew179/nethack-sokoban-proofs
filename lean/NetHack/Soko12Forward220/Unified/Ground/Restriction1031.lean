import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1031_0_checked : (List.range' 527872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1031_1_checked : (List.range' 528000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1031_2_checked : (List.range' 528128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1031_3_checked : (List.range' 528256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1031_range (index : Nat) (lower : 527872 ≤ index) (upper : index < 528384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 528128 then
    if cut : index < 528000 then
      exact segment_sound _ 527872 128 Restriction1031_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 528000 128 Restriction1031_1_checked index (by omega) (by omega)
  else
    if cut : index < 528256 then
      exact segment_sound _ 528128 128 Restriction1031_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 528256 128 Restriction1031_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
