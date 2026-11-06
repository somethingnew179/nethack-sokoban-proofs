import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0050_0_checked : (List.range' 25600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0050_1_checked : (List.range' 25728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0050_2_checked : (List.range' 25856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0050_3_checked : (List.range' 25984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0050_range (index : Nat) (lower : 25600 ≤ index) (upper : index < 26112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 25856 then
    if cut : index < 25728 then
      exact segment_sound _ 25600 128 Restriction0050_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25728 128 Restriction0050_1_checked index (by omega) (by omega)
  else
    if cut : index < 25984 then
      exact segment_sound _ 25856 128 Restriction0050_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25984 128 Restriction0050_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
