import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1122_0_checked : (List.range' 574464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1122_1_checked : (List.range' 574592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1122_2_checked : (List.range' 574720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1122_3_checked : (List.range' 574848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1122_range (index : Nat) (lower : 574464 ≤ index) (upper : index < 574976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 574720 then
    if cut : index < 574592 then
      exact segment_sound _ 574464 128 Restriction1122_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 574592 128 Restriction1122_1_checked index (by omega) (by omega)
  else
    if cut : index < 574848 then
      exact segment_sound _ 574720 128 Restriction1122_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 574848 128 Restriction1122_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
