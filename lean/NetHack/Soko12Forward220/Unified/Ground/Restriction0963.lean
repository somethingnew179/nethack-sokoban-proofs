import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0963_0_checked : (List.range' 493056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0963_1_checked : (List.range' 493184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0963_2_checked : (List.range' 493312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0963_3_checked : (List.range' 493440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0963_range (index : Nat) (lower : 493056 ≤ index) (upper : index < 493568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 493312 then
    if cut : index < 493184 then
      exact segment_sound _ 493056 128 Restriction0963_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 493184 128 Restriction0963_1_checked index (by omega) (by omega)
  else
    if cut : index < 493440 then
      exact segment_sound _ 493312 128 Restriction0963_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 493440 128 Restriction0963_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
