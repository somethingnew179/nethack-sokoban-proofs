import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0695_0_checked : (List.range' 355840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0695_1_checked : (List.range' 355968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0695_2_checked : (List.range' 356096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0695_3_checked : (List.range' 356224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0695_range (index : Nat) (lower : 355840 ≤ index) (upper : index < 356352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 356096 then
    if cut : index < 355968 then
      exact segment_sound _ 355840 128 Restriction0695_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 355968 128 Restriction0695_1_checked index (by omega) (by omega)
  else
    if cut : index < 356224 then
      exact segment_sound _ 356096 128 Restriction0695_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 356224 128 Restriction0695_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
