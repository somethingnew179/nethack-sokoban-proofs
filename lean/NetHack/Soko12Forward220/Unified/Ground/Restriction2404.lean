import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2404_0_checked : (List.range' 1230848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2404_1_checked : (List.range' 1230976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2404_2_checked : (List.range' 1231104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2404_3_checked : (List.range' 1231232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2404_range (index : Nat) (lower : 1230848 ≤ index) (upper : index < 1231360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1231104 then
    if cut : index < 1230976 then
      exact segment_sound _ 1230848 128 Restriction2404_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1230976 128 Restriction2404_1_checked index (by omega) (by omega)
  else
    if cut : index < 1231232 then
      exact segment_sound _ 1231104 128 Restriction2404_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1231232 128 Restriction2404_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
