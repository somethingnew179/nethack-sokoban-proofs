import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0535_0_checked : (List.range' 273920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0535_1_checked : (List.range' 274048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0535_2_checked : (List.range' 274176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0535_3_checked : (List.range' 274304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0535_range (index : Nat) (lower : 273920 ≤ index) (upper : index < 274432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 274176 then
    if cut : index < 274048 then
      exact segment_sound _ 273920 128 Restriction0535_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 274048 128 Restriction0535_1_checked index (by omega) (by omega)
  else
    if cut : index < 274304 then
      exact segment_sound _ 274176 128 Restriction0535_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 274304 128 Restriction0535_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
