import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1116_0_checked : (List.range' 571392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1116_1_checked : (List.range' 571520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1116_2_checked : (List.range' 571648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1116_3_checked : (List.range' 571776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1116_range (index : Nat) (lower : 571392 ≤ index) (upper : index < 571904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 571648 then
    if cut : index < 571520 then
      exact segment_sound _ 571392 128 Restriction1116_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 571520 128 Restriction1116_1_checked index (by omega) (by omega)
  else
    if cut : index < 571776 then
      exact segment_sound _ 571648 128 Restriction1116_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 571776 128 Restriction1116_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
