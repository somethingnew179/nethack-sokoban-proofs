import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0537_0_checked : (List.range' 274944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0537_1_checked : (List.range' 275072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0537_2_checked : (List.range' 275200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0537_3_checked : (List.range' 275328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0537_range (index : Nat) (lower : 274944 ≤ index) (upper : index < 275456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 275200 then
    if cut : index < 275072 then
      exact segment_sound _ 274944 128 Restriction0537_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275072 128 Restriction0537_1_checked index (by omega) (by omega)
  else
    if cut : index < 275328 then
      exact segment_sound _ 275200 128 Restriction0537_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275328 128 Restriction0537_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
