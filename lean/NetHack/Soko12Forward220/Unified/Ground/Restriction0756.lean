import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0756_0_checked : (List.range' 387072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0756_1_checked : (List.range' 387200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0756_2_checked : (List.range' 387328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0756_3_checked : (List.range' 387456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0756_range (index : Nat) (lower : 387072 ≤ index) (upper : index < 387584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 387328 then
    if cut : index < 387200 then
      exact segment_sound _ 387072 128 Restriction0756_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 387200 128 Restriction0756_1_checked index (by omega) (by omega)
  else
    if cut : index < 387456 then
      exact segment_sound _ 387328 128 Restriction0756_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 387456 128 Restriction0756_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
