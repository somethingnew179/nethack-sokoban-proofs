import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0726_0_checked : (List.range' 371712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0726_1_checked : (List.range' 371840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0726_2_checked : (List.range' 371968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0726_3_checked : (List.range' 372096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0726_range (index : Nat) (lower : 371712 ≤ index) (upper : index < 372224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 371968 then
    if cut : index < 371840 then
      exact segment_sound _ 371712 128 Restriction0726_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 371840 128 Restriction0726_1_checked index (by omega) (by omega)
  else
    if cut : index < 372096 then
      exact segment_sound _ 371968 128 Restriction0726_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 372096 128 Restriction0726_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
