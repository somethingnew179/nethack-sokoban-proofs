import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0161_0_checked : (List.range' 82432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0161_1_checked : (List.range' 82560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0161_2_checked : (List.range' 82688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0161_3_checked : (List.range' 82816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0161_range (index : Nat) (lower : 82432 ≤ index) (upper : index < 82944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 82688 then
    if cut : index < 82560 then
      exact segment_sound _ 82432 128 Restriction0161_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 82560 128 Restriction0161_1_checked index (by omega) (by omega)
  else
    if cut : index < 82816 then
      exact segment_sound _ 82688 128 Restriction0161_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 82816 128 Restriction0161_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
