import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2442_0_checked : (List.range' 1250304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2442_1_checked : (List.range' 1250432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2442_2_checked : (List.range' 1250560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2442_3_checked : (List.range' 1250688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2442_range (index : Nat) (lower : 1250304 ≤ index) (upper : index < 1250816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1250560 then
    if cut : index < 1250432 then
      exact segment_sound _ 1250304 128 Restriction2442_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1250432 128 Restriction2442_1_checked index (by omega) (by omega)
  else
    if cut : index < 1250688 then
      exact segment_sound _ 1250560 128 Restriction2442_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1250688 128 Restriction2442_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
