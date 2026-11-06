import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1467_0_checked : (List.range' 751104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1467_1_checked : (List.range' 751232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1467_2_checked : (List.range' 751360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1467_3_checked : (List.range' 751488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1467_range (index : Nat) (lower : 751104 ≤ index) (upper : index < 751616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 751360 then
    if cut : index < 751232 then
      exact segment_sound _ 751104 128 Restriction1467_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 751232 128 Restriction1467_1_checked index (by omega) (by omega)
  else
    if cut : index < 751488 then
      exact segment_sound _ 751360 128 Restriction1467_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 751488 128 Restriction1467_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
