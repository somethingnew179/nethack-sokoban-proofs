import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0078_0_checked : (List.range' 39936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0078_1_checked : (List.range' 40064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0078_2_checked : (List.range' 40192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0078_3_checked : (List.range' 40320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0078_range (index : Nat) (lower : 39936 ≤ index) (upper : index < 40448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 40192 then
    if cut : index < 40064 then
      exact segment_sound _ 39936 128 Restriction0078_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 40064 128 Restriction0078_1_checked index (by omega) (by omega)
  else
    if cut : index < 40320 then
      exact segment_sound _ 40192 128 Restriction0078_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 40320 128 Restriction0078_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
