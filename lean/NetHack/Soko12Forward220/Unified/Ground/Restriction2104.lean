import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2104_0_checked : (List.range' 1077248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2104_1_checked : (List.range' 1077376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2104_2_checked : (List.range' 1077504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2104_3_checked : (List.range' 1077632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2104_range (index : Nat) (lower : 1077248 ≤ index) (upper : index < 1077760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1077504 then
    if cut : index < 1077376 then
      exact segment_sound _ 1077248 128 Restriction2104_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1077376 128 Restriction2104_1_checked index (by omega) (by omega)
  else
    if cut : index < 1077632 then
      exact segment_sound _ 1077504 128 Restriction2104_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1077632 128 Restriction2104_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
