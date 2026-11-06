import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0717_0_checked : (List.range' 367104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0717_1_checked : (List.range' 367232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0717_2_checked : (List.range' 367360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0717_3_checked : (List.range' 367488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0717_range (index : Nat) (lower : 367104 ≤ index) (upper : index < 367616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 367360 then
    if cut : index < 367232 then
      exact segment_sound _ 367104 128 Restriction0717_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 367232 128 Restriction0717_1_checked index (by omega) (by omega)
  else
    if cut : index < 367488 then
      exact segment_sound _ 367360 128 Restriction0717_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 367488 128 Restriction0717_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
