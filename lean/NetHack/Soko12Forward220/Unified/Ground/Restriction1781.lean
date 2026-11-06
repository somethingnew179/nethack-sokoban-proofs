import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1781_0_checked : (List.range' 911872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1781_1_checked : (List.range' 912000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1781_2_checked : (List.range' 912128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1781_3_checked : (List.range' 912256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1781_range (index : Nat) (lower : 911872 ≤ index) (upper : index < 912384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 912128 then
    if cut : index < 912000 then
      exact segment_sound _ 911872 128 Restriction1781_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 912000 128 Restriction1781_1_checked index (by omega) (by omega)
  else
    if cut : index < 912256 then
      exact segment_sound _ 912128 128 Restriction1781_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 912256 128 Restriction1781_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
