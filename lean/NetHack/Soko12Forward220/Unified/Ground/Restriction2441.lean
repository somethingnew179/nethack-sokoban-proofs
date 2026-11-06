import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2441_0_checked : (List.range' 1249792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2441_1_checked : (List.range' 1249920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2441_2_checked : (List.range' 1250048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2441_3_checked : (List.range' 1250176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2441_range (index : Nat) (lower : 1249792 ≤ index) (upper : index < 1250304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1250048 then
    if cut : index < 1249920 then
      exact segment_sound _ 1249792 128 Restriction2441_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1249920 128 Restriction2441_1_checked index (by omega) (by omega)
  else
    if cut : index < 1250176 then
      exact segment_sound _ 1250048 128 Restriction2441_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1250176 128 Restriction2441_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
