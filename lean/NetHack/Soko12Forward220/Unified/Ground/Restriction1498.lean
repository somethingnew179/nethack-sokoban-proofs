import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1498_0_checked : (List.range' 766976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1498_1_checked : (List.range' 767104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1498_2_checked : (List.range' 767232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1498_3_checked : (List.range' 767360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1498_range (index : Nat) (lower : 766976 ≤ index) (upper : index < 767488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 767232 then
    if cut : index < 767104 then
      exact segment_sound _ 766976 128 Restriction1498_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 767104 128 Restriction1498_1_checked index (by omega) (by omega)
  else
    if cut : index < 767360 then
      exact segment_sound _ 767232 128 Restriction1498_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 767360 128 Restriction1498_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
