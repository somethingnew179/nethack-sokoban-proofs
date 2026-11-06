import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0789_0_checked : (List.range' 403968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0789_1_checked : (List.range' 404096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0789_2_checked : (List.range' 404224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0789_3_checked : (List.range' 404352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0789_range (index : Nat) (lower : 403968 ≤ index) (upper : index < 404480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 404224 then
    if cut : index < 404096 then
      exact segment_sound _ 403968 128 Restriction0789_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 404096 128 Restriction0789_1_checked index (by omega) (by omega)
  else
    if cut : index < 404352 then
      exact segment_sound _ 404224 128 Restriction0789_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 404352 128 Restriction0789_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
