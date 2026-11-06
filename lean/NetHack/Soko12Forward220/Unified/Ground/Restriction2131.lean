import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2131_0_checked : (List.range' 1091072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2131_1_checked : (List.range' 1091200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2131_2_checked : (List.range' 1091328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2131_3_checked : (List.range' 1091456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2131_range (index : Nat) (lower : 1091072 ≤ index) (upper : index < 1091584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1091328 then
    if cut : index < 1091200 then
      exact segment_sound _ 1091072 128 Restriction2131_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1091200 128 Restriction2131_1_checked index (by omega) (by omega)
  else
    if cut : index < 1091456 then
      exact segment_sound _ 1091328 128 Restriction2131_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1091456 128 Restriction2131_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
