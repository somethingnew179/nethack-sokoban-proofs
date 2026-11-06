import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1782_0_checked : (List.range' 912384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1782_1_checked : (List.range' 912512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1782_2_checked : (List.range' 912640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1782_3_checked : (List.range' 912768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1782_range (index : Nat) (lower : 912384 ≤ index) (upper : index < 912896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 912640 then
    if cut : index < 912512 then
      exact segment_sound _ 912384 128 Restriction1782_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 912512 128 Restriction1782_1_checked index (by omega) (by omega)
  else
    if cut : index < 912768 then
      exact segment_sound _ 912640 128 Restriction1782_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 912768 128 Restriction1782_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
