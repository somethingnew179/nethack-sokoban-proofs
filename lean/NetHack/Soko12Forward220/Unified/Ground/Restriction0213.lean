import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0213_0_checked : (List.range' 109056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0213_1_checked : (List.range' 109184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0213_2_checked : (List.range' 109312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0213_3_checked : (List.range' 109440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0213_range (index : Nat) (lower : 109056 ≤ index) (upper : index < 109568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 109312 then
    if cut : index < 109184 then
      exact segment_sound _ 109056 128 Restriction0213_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109184 128 Restriction0213_1_checked index (by omega) (by omega)
  else
    if cut : index < 109440 then
      exact segment_sound _ 109312 128 Restriction0213_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109440 128 Restriction0213_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
