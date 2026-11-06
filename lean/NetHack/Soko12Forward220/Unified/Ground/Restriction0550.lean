import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0550_0_checked : (List.range' 281600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0550_1_checked : (List.range' 281728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0550_2_checked : (List.range' 281856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0550_3_checked : (List.range' 281984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0550_range (index : Nat) (lower : 281600 ≤ index) (upper : index < 282112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 281856 then
    if cut : index < 281728 then
      exact segment_sound _ 281600 128 Restriction0550_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281728 128 Restriction0550_1_checked index (by omega) (by omega)
  else
    if cut : index < 281984 then
      exact segment_sound _ 281856 128 Restriction0550_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 281984 128 Restriction0550_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
