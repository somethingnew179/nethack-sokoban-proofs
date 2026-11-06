import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1115_0_checked : (List.range' 570880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1115_1_checked : (List.range' 571008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1115_2_checked : (List.range' 571136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1115_3_checked : (List.range' 571264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1115_range (index : Nat) (lower : 570880 ≤ index) (upper : index < 571392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 571136 then
    if cut : index < 571008 then
      exact segment_sound _ 570880 128 Restriction1115_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 571008 128 Restriction1115_1_checked index (by omega) (by omega)
  else
    if cut : index < 571264 then
      exact segment_sound _ 571136 128 Restriction1115_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 571264 128 Restriction1115_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
