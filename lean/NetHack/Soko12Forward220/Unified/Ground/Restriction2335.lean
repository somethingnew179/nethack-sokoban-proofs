import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2335_0_checked : (List.range' 1195520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2335_1_checked : (List.range' 1195648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2335_2_checked : (List.range' 1195776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2335_3_checked : (List.range' 1195904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2335_range (index : Nat) (lower : 1195520 ≤ index) (upper : index < 1196032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1195776 then
    if cut : index < 1195648 then
      exact segment_sound _ 1195520 128 Restriction2335_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1195648 128 Restriction2335_1_checked index (by omega) (by omega)
  else
    if cut : index < 1195904 then
      exact segment_sound _ 1195776 128 Restriction2335_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1195904 128 Restriction2335_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
