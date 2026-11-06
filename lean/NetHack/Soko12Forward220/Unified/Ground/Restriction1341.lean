import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1341_0_checked : (List.range' 686592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1341_1_checked : (List.range' 686720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1341_2_checked : (List.range' 686848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1341_3_checked : (List.range' 686976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1341_range (index : Nat) (lower : 686592 ≤ index) (upper : index < 687104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 686848 then
    if cut : index < 686720 then
      exact segment_sound _ 686592 128 Restriction1341_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 686720 128 Restriction1341_1_checked index (by omega) (by omega)
  else
    if cut : index < 686976 then
      exact segment_sound _ 686848 128 Restriction1341_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 686976 128 Restriction1341_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
