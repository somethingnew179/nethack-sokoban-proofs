import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0348_0_checked : (List.range' 178176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0348_1_checked : (List.range' 178304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0348_2_checked : (List.range' 178432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0348_3_checked : (List.range' 178560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0348_range (index : Nat) (lower : 178176 ≤ index) (upper : index < 178688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 178432 then
    if cut : index < 178304 then
      exact segment_sound _ 178176 128 Restriction0348_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178304 128 Restriction0348_1_checked index (by omega) (by omega)
  else
    if cut : index < 178560 then
      exact segment_sound _ 178432 128 Restriction0348_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178560 128 Restriction0348_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
