import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2032_0_checked : (List.range' 1040384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2032_1_checked : (List.range' 1040512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2032_2_checked : (List.range' 1040640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2032_3_checked : (List.range' 1040768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2032_range (index : Nat) (lower : 1040384 ≤ index) (upper : index < 1040896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1040640 then
    if cut : index < 1040512 then
      exact segment_sound _ 1040384 128 Restriction2032_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1040512 128 Restriction2032_1_checked index (by omega) (by omega)
  else
    if cut : index < 1040768 then
      exact segment_sound _ 1040640 128 Restriction2032_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1040768 128 Restriction2032_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
