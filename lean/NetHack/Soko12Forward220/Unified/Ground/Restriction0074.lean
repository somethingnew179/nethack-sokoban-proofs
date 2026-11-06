import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0074_0_checked : (List.range' 37888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0074_1_checked : (List.range' 38016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0074_2_checked : (List.range' 38144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0074_3_checked : (List.range' 38272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0074_range (index : Nat) (lower : 37888 ≤ index) (upper : index < 38400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 38144 then
    if cut : index < 38016 then
      exact segment_sound _ 37888 128 Restriction0074_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38016 128 Restriction0074_1_checked index (by omega) (by omega)
  else
    if cut : index < 38272 then
      exact segment_sound _ 38144 128 Restriction0074_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38272 128 Restriction0074_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
