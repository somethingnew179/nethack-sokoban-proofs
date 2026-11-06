import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2146_0_checked : (List.range' 1098752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2146_1_checked : (List.range' 1098880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2146_2_checked : (List.range' 1099008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2146_3_checked : (List.range' 1099136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2146_range (index : Nat) (lower : 1098752 ≤ index) (upper : index < 1099264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1099008 then
    if cut : index < 1098880 then
      exact segment_sound _ 1098752 128 Restriction2146_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1098880 128 Restriction2146_1_checked index (by omega) (by omega)
  else
    if cut : index < 1099136 then
      exact segment_sound _ 1099008 128 Restriction2146_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1099136 128 Restriction2146_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
