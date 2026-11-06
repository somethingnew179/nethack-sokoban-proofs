import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1690_0_checked : (List.range' 865280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1690_1_checked : (List.range' 865408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1690_2_checked : (List.range' 865536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1690_3_checked : (List.range' 865664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1690_range (index : Nat) (lower : 865280 ≤ index) (upper : index < 865792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 865536 then
    if cut : index < 865408 then
      exact segment_sound _ 865280 128 Restriction1690_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 865408 128 Restriction1690_1_checked index (by omega) (by omega)
  else
    if cut : index < 865664 then
      exact segment_sound _ 865536 128 Restriction1690_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 865664 128 Restriction1690_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
