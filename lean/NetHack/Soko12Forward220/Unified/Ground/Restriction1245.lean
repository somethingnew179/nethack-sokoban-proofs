import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1245_0_checked : (List.range' 637440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1245_1_checked : (List.range' 637568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1245_2_checked : (List.range' 637696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1245_3_checked : (List.range' 637824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1245_range (index : Nat) (lower : 637440 ≤ index) (upper : index < 637952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 637696 then
    if cut : index < 637568 then
      exact segment_sound _ 637440 128 Restriction1245_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 637568 128 Restriction1245_1_checked index (by omega) (by omega)
  else
    if cut : index < 637824 then
      exact segment_sound _ 637696 128 Restriction1245_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 637824 128 Restriction1245_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
