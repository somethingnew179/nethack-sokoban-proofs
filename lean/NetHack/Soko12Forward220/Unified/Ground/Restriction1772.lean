import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1772_0_checked : (List.range' 907264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1772_1_checked : (List.range' 907392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1772_2_checked : (List.range' 907520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1772_3_checked : (List.range' 907648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1772_range (index : Nat) (lower : 907264 ≤ index) (upper : index < 907776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 907520 then
    if cut : index < 907392 then
      exact segment_sound _ 907264 128 Restriction1772_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 907392 128 Restriction1772_1_checked index (by omega) (by omega)
  else
    if cut : index < 907648 then
      exact segment_sound _ 907520 128 Restriction1772_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 907648 128 Restriction1772_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
