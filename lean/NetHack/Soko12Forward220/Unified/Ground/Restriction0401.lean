import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0401_0_checked : (List.range' 205312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0401_1_checked : (List.range' 205440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0401_2_checked : (List.range' 205568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0401_3_checked : (List.range' 205696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0401_range (index : Nat) (lower : 205312 ≤ index) (upper : index < 205824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 205568 then
    if cut : index < 205440 then
      exact segment_sound _ 205312 128 Restriction0401_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 205440 128 Restriction0401_1_checked index (by omega) (by omega)
  else
    if cut : index < 205696 then
      exact segment_sound _ 205568 128 Restriction0401_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 205696 128 Restriction0401_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
