import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2569_0_checked : (List.range' 1315328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2569_1_checked : (List.range' 1315456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2569_2_checked : (List.range' 1315584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2569_3_checked : (List.range' 1315712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2569_range (index : Nat) (lower : 1315328 ≤ index) (upper : index < 1315840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1315584 then
    if cut : index < 1315456 then
      exact segment_sound _ 1315328 128 Restriction2569_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1315456 128 Restriction2569_1_checked index (by omega) (by omega)
  else
    if cut : index < 1315712 then
      exact segment_sound _ 1315584 128 Restriction2569_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1315712 128 Restriction2569_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
