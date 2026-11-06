import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0347_0_checked : (List.range' 177664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0347_1_checked : (List.range' 177792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0347_2_checked : (List.range' 177920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0347_3_checked : (List.range' 178048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0347_range (index : Nat) (lower : 177664 ≤ index) (upper : index < 178176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 177920 then
    if cut : index < 177792 then
      exact segment_sound _ 177664 128 Restriction0347_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 177792 128 Restriction0347_1_checked index (by omega) (by omega)
  else
    if cut : index < 178048 then
      exact segment_sound _ 177920 128 Restriction0347_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178048 128 Restriction0347_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
