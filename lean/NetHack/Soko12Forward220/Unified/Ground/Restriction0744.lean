import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0744_0_checked : (List.range' 380928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0744_1_checked : (List.range' 381056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0744_2_checked : (List.range' 381184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0744_3_checked : (List.range' 381312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0744_range (index : Nat) (lower : 380928 ≤ index) (upper : index < 381440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 381184 then
    if cut : index < 381056 then
      exact segment_sound _ 380928 128 Restriction0744_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 381056 128 Restriction0744_1_checked index (by omega) (by omega)
  else
    if cut : index < 381312 then
      exact segment_sound _ 381184 128 Restriction0744_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 381312 128 Restriction0744_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
