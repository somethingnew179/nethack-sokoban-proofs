import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2033_0_checked : (List.range' 1040896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2033_1_checked : (List.range' 1041024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2033_2_checked : (List.range' 1041152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2033_3_checked : (List.range' 1041280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2033_range (index : Nat) (lower : 1040896 ≤ index) (upper : index < 1041408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1041152 then
    if cut : index < 1041024 then
      exact segment_sound _ 1040896 128 Restriction2033_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1041024 128 Restriction2033_1_checked index (by omega) (by omega)
  else
    if cut : index < 1041280 then
      exact segment_sound _ 1041152 128 Restriction2033_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1041280 128 Restriction2033_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
