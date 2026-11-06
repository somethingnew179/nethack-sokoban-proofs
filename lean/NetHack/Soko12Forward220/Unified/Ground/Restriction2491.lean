import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2491_0_checked : (List.range' 1275392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2491_1_checked : (List.range' 1275520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2491_2_checked : (List.range' 1275648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2491_3_checked : (List.range' 1275776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2491_range (index : Nat) (lower : 1275392 ≤ index) (upper : index < 1275904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1275648 then
    if cut : index < 1275520 then
      exact segment_sound _ 1275392 128 Restriction2491_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1275520 128 Restriction2491_1_checked index (by omega) (by omega)
  else
    if cut : index < 1275776 then
      exact segment_sound _ 1275648 128 Restriction2491_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1275776 128 Restriction2491_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
