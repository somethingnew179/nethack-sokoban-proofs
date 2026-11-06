import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0699_0_checked : (List.range' 357888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0699_1_checked : (List.range' 358016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0699_2_checked : (List.range' 358144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0699_3_checked : (List.range' 358272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0699_range (index : Nat) (lower : 357888 ≤ index) (upper : index < 358400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 358144 then
    if cut : index < 358016 then
      exact segment_sound _ 357888 128 Restriction0699_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 358016 128 Restriction0699_1_checked index (by omega) (by omega)
  else
    if cut : index < 358272 then
      exact segment_sound _ 358144 128 Restriction0699_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 358272 128 Restriction0699_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
