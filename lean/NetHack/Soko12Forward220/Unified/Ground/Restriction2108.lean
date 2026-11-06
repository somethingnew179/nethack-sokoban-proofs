import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2108_0_checked : (List.range' 1079296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2108_1_checked : (List.range' 1079424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2108_2_checked : (List.range' 1079552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2108_3_checked : (List.range' 1079680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2108_range (index : Nat) (lower : 1079296 ≤ index) (upper : index < 1079808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1079552 then
    if cut : index < 1079424 then
      exact segment_sound _ 1079296 128 Restriction2108_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1079424 128 Restriction2108_1_checked index (by omega) (by omega)
  else
    if cut : index < 1079680 then
      exact segment_sound _ 1079552 128 Restriction2108_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1079680 128 Restriction2108_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
