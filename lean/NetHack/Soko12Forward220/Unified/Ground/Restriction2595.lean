import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2595_0_checked : (List.range' 1328640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2595_1_checked : (List.range' 1328768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2595_2_checked : (List.range' 1328896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2595_3_checked : (List.range' 1329024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2595_range (index : Nat) (lower : 1328640 ≤ index) (upper : index < 1329152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1328896 then
    if cut : index < 1328768 then
      exact segment_sound _ 1328640 128 Restriction2595_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1328768 128 Restriction2595_1_checked index (by omega) (by omega)
  else
    if cut : index < 1329024 then
      exact segment_sound _ 1328896 128 Restriction2595_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1329024 128 Restriction2595_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
