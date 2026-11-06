import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1130_0_checked : (List.range' 578560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1130_1_checked : (List.range' 578688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1130_2_checked : (List.range' 578816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1130_3_checked : (List.range' 578944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1130_range (index : Nat) (lower : 578560 ≤ index) (upper : index < 579072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 578816 then
    if cut : index < 578688 then
      exact segment_sound _ 578560 128 Restriction1130_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 578688 128 Restriction1130_1_checked index (by omega) (by omega)
  else
    if cut : index < 578944 then
      exact segment_sound _ 578816 128 Restriction1130_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 578944 128 Restriction1130_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
