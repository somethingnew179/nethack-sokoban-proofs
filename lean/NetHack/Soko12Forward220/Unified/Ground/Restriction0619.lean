import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0619_0_checked : (List.range' 316928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0619_1_checked : (List.range' 317056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0619_2_checked : (List.range' 317184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0619_3_checked : (List.range' 317312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0619_range (index : Nat) (lower : 316928 ≤ index) (upper : index < 317440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 317184 then
    if cut : index < 317056 then
      exact segment_sound _ 316928 128 Restriction0619_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 317056 128 Restriction0619_1_checked index (by omega) (by omega)
  else
    if cut : index < 317312 then
      exact segment_sound _ 317184 128 Restriction0619_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 317312 128 Restriction0619_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
