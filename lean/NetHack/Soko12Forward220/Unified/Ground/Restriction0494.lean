import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0494_0_checked : (List.range' 252928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0494_1_checked : (List.range' 253056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0494_2_checked : (List.range' 253184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0494_3_checked : (List.range' 253312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0494_range (index : Nat) (lower : 252928 ≤ index) (upper : index < 253440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 253184 then
    if cut : index < 253056 then
      exact segment_sound _ 252928 128 Restriction0494_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 253056 128 Restriction0494_1_checked index (by omega) (by omega)
  else
    if cut : index < 253312 then
      exact segment_sound _ 253184 128 Restriction0494_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 253312 128 Restriction0494_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
