import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0850_0_checked : (List.range' 435200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0850_1_checked : (List.range' 435328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0850_2_checked : (List.range' 435456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0850_3_checked : (List.range' 435584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0850_range (index : Nat) (lower : 435200 ≤ index) (upper : index < 435712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 435456 then
    if cut : index < 435328 then
      exact segment_sound _ 435200 128 Restriction0850_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 435328 128 Restriction0850_1_checked index (by omega) (by omega)
  else
    if cut : index < 435584 then
      exact segment_sound _ 435456 128 Restriction0850_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 435584 128 Restriction0850_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
