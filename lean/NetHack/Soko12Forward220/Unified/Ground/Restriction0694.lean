import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0694_0_checked : (List.range' 355328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0694_1_checked : (List.range' 355456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0694_2_checked : (List.range' 355584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0694_3_checked : (List.range' 355712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0694_range (index : Nat) (lower : 355328 ≤ index) (upper : index < 355840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 355584 then
    if cut : index < 355456 then
      exact segment_sound _ 355328 128 Restriction0694_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 355456 128 Restriction0694_1_checked index (by omega) (by omega)
  else
    if cut : index < 355712 then
      exact segment_sound _ 355584 128 Restriction0694_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 355712 128 Restriction0694_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
