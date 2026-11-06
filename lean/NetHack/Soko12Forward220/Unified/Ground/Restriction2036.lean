import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2036_0_checked : (List.range' 1042432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2036_1_checked : (List.range' 1042560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2036_2_checked : (List.range' 1042688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2036_3_checked : (List.range' 1042816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2036_range (index : Nat) (lower : 1042432 ≤ index) (upper : index < 1042944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1042688 then
    if cut : index < 1042560 then
      exact segment_sound _ 1042432 128 Restriction2036_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1042560 128 Restriction2036_1_checked index (by omega) (by omega)
  else
    if cut : index < 1042816 then
      exact segment_sound _ 1042688 128 Restriction2036_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1042816 128 Restriction2036_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
