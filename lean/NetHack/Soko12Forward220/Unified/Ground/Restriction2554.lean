import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2554_0_checked : (List.range' 1307648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2554_1_checked : (List.range' 1307776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2554_2_checked : (List.range' 1307904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2554_3_checked : (List.range' 1308032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2554_range (index : Nat) (lower : 1307648 ≤ index) (upper : index < 1308160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1307904 then
    if cut : index < 1307776 then
      exact segment_sound _ 1307648 128 Restriction2554_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1307776 128 Restriction2554_1_checked index (by omega) (by omega)
  else
    if cut : index < 1308032 then
      exact segment_sound _ 1307904 128 Restriction2554_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1308032 128 Restriction2554_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
