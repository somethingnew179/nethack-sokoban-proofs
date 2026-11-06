import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1040_0_checked : (List.range' 532480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1040_1_checked : (List.range' 532608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1040_2_checked : (List.range' 532736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1040_3_checked : (List.range' 532864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1040_range (index : Nat) (lower : 532480 ≤ index) (upper : index < 532992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 532736 then
    if cut : index < 532608 then
      exact segment_sound _ 532480 128 Restriction1040_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 532608 128 Restriction1040_1_checked index (by omega) (by omega)
  else
    if cut : index < 532864 then
      exact segment_sound _ 532736 128 Restriction1040_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 532864 128 Restriction1040_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
