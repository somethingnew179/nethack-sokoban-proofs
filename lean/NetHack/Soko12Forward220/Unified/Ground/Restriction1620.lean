import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1620_0_checked : (List.range' 829440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1620_1_checked : (List.range' 829568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1620_2_checked : (List.range' 829696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1620_3_checked : (List.range' 829824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1620_range (index : Nat) (lower : 829440 ≤ index) (upper : index < 829952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 829696 then
    if cut : index < 829568 then
      exact segment_sound _ 829440 128 Restriction1620_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 829568 128 Restriction1620_1_checked index (by omega) (by omega)
  else
    if cut : index < 829824 then
      exact segment_sound _ 829696 128 Restriction1620_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 829824 128 Restriction1620_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
