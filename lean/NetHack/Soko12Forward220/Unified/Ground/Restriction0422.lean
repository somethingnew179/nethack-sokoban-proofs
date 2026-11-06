import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0422_0_checked : (List.range' 216064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0422_1_checked : (List.range' 216192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0422_2_checked : (List.range' 216320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0422_3_checked : (List.range' 216448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0422_range (index : Nat) (lower : 216064 ≤ index) (upper : index < 216576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 216320 then
    if cut : index < 216192 then
      exact segment_sound _ 216064 128 Restriction0422_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216192 128 Restriction0422_1_checked index (by omega) (by omega)
  else
    if cut : index < 216448 then
      exact segment_sound _ 216320 128 Restriction0422_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216448 128 Restriction0422_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
