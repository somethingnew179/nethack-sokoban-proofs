import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0761_0_checked : (List.range' 389632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0761_1_checked : (List.range' 389760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0761_2_checked : (List.range' 389888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0761_3_checked : (List.range' 390016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0761_range (index : Nat) (lower : 389632 ≤ index) (upper : index < 390144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 389888 then
    if cut : index < 389760 then
      exact segment_sound _ 389632 128 Restriction0761_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 389760 128 Restriction0761_1_checked index (by omega) (by omega)
  else
    if cut : index < 390016 then
      exact segment_sound _ 389888 128 Restriction0761_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 390016 128 Restriction0761_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
