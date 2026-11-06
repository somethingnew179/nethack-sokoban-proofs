import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2148_0_checked : (List.range' 1099776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2148_1_checked : (List.range' 1099904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2148_2_checked : (List.range' 1100032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2148_3_checked : (List.range' 1100160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2148_range (index : Nat) (lower : 1099776 ≤ index) (upper : index < 1100288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1100032 then
    if cut : index < 1099904 then
      exact segment_sound _ 1099776 128 Restriction2148_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1099904 128 Restriction2148_1_checked index (by omega) (by omega)
  else
    if cut : index < 1100160 then
      exact segment_sound _ 1100032 128 Restriction2148_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1100160 128 Restriction2148_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
