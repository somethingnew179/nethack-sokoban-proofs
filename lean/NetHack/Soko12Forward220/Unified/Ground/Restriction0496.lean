import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0496_0_checked : (List.range' 253952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0496_1_checked : (List.range' 254080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0496_2_checked : (List.range' 254208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0496_3_checked : (List.range' 254336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0496_range (index : Nat) (lower : 253952 ≤ index) (upper : index < 254464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 254208 then
    if cut : index < 254080 then
      exact segment_sound _ 253952 128 Restriction0496_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 254080 128 Restriction0496_1_checked index (by omega) (by omega)
  else
    if cut : index < 254336 then
      exact segment_sound _ 254208 128 Restriction0496_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 254336 128 Restriction0496_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
