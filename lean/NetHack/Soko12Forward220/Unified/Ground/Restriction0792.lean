import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0792_0_checked : (List.range' 405504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0792_1_checked : (List.range' 405632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0792_2_checked : (List.range' 405760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0792_3_checked : (List.range' 405888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0792_range (index : Nat) (lower : 405504 ≤ index) (upper : index < 406016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 405760 then
    if cut : index < 405632 then
      exact segment_sound _ 405504 128 Restriction0792_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 405632 128 Restriction0792_1_checked index (by omega) (by omega)
  else
    if cut : index < 405888 then
      exact segment_sound _ 405760 128 Restriction0792_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 405888 128 Restriction0792_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
