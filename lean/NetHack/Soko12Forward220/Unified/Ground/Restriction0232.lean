import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0232_0_checked : (List.range' 118784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0232_1_checked : (List.range' 118912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0232_2_checked : (List.range' 119040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0232_3_checked : (List.range' 119168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0232_range (index : Nat) (lower : 118784 ≤ index) (upper : index < 119296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 119040 then
    if cut : index < 118912 then
      exact segment_sound _ 118784 128 Restriction0232_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 118912 128 Restriction0232_1_checked index (by omega) (by omega)
  else
    if cut : index < 119168 then
      exact segment_sound _ 119040 128 Restriction0232_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 119168 128 Restriction0232_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
