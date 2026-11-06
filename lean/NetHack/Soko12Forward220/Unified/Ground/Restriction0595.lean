import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0595_0_checked : (List.range' 304640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0595_1_checked : (List.range' 304768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0595_2_checked : (List.range' 304896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0595_3_checked : (List.range' 305024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0595_range (index : Nat) (lower : 304640 ≤ index) (upper : index < 305152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 304896 then
    if cut : index < 304768 then
      exact segment_sound _ 304640 128 Restriction0595_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 304768 128 Restriction0595_1_checked index (by omega) (by omega)
  else
    if cut : index < 305024 then
      exact segment_sound _ 304896 128 Restriction0595_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 305024 128 Restriction0595_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
