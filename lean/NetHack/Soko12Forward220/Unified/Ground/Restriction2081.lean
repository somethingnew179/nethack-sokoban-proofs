import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2081_0_checked : (List.range' 1065472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2081_1_checked : (List.range' 1065600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2081_2_checked : (List.range' 1065728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2081_3_checked : (List.range' 1065856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2081_range (index : Nat) (lower : 1065472 ≤ index) (upper : index < 1065984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1065728 then
    if cut : index < 1065600 then
      exact segment_sound _ 1065472 128 Restriction2081_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1065600 128 Restriction2081_1_checked index (by omega) (by omega)
  else
    if cut : index < 1065856 then
      exact segment_sound _ 1065728 128 Restriction2081_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1065856 128 Restriction2081_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
