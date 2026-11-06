import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0975_0_checked : (List.range' 499200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0975_1_checked : (List.range' 499328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0975_2_checked : (List.range' 499456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0975_3_checked : (List.range' 499584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0975_range (index : Nat) (lower : 499200 ≤ index) (upper : index < 499712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 499456 then
    if cut : index < 499328 then
      exact segment_sound _ 499200 128 Restriction0975_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 499328 128 Restriction0975_1_checked index (by omega) (by omega)
  else
    if cut : index < 499584 then
      exact segment_sound _ 499456 128 Restriction0975_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 499584 128 Restriction0975_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
