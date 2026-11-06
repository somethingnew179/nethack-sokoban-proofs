import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0261_0_checked : (List.range' 133632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0261_1_checked : (List.range' 133760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0261_2_checked : (List.range' 133888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0261_3_checked : (List.range' 134016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0261_range (index : Nat) (lower : 133632 ≤ index) (upper : index < 134144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 133888 then
    if cut : index < 133760 then
      exact segment_sound _ 133632 128 Restriction0261_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 133760 128 Restriction0261_1_checked index (by omega) (by omega)
  else
    if cut : index < 134016 then
      exact segment_sound _ 133888 128 Restriction0261_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 134016 128 Restriction0261_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
