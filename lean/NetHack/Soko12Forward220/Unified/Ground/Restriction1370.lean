import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1370_0_checked : (List.range' 701440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1370_1_checked : (List.range' 701568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1370_2_checked : (List.range' 701696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1370_3_checked : (List.range' 701824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1370_range (index : Nat) (lower : 701440 ≤ index) (upper : index < 701952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 701696 then
    if cut : index < 701568 then
      exact segment_sound _ 701440 128 Restriction1370_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 701568 128 Restriction1370_1_checked index (by omega) (by omega)
  else
    if cut : index < 701824 then
      exact segment_sound _ 701696 128 Restriction1370_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 701824 128 Restriction1370_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
