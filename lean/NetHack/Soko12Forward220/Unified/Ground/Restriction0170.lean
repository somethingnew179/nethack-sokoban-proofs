import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0170_0_checked : (List.range' 87040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0170_1_checked : (List.range' 87168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0170_2_checked : (List.range' 87296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0170_3_checked : (List.range' 87424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0170_range (index : Nat) (lower : 87040 ≤ index) (upper : index < 87552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 87296 then
    if cut : index < 87168 then
      exact segment_sound _ 87040 128 Restriction0170_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 87168 128 Restriction0170_1_checked index (by omega) (by omega)
  else
    if cut : index < 87424 then
      exact segment_sound _ 87296 128 Restriction0170_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 87424 128 Restriction0170_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
