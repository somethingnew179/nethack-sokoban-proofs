import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2050_0_checked : (List.range' 1049600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2050_1_checked : (List.range' 1049728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2050_2_checked : (List.range' 1049856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2050_3_checked : (List.range' 1049984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2050_range (index : Nat) (lower : 1049600 ≤ index) (upper : index < 1050112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1049856 then
    if cut : index < 1049728 then
      exact segment_sound _ 1049600 128 Restriction2050_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1049728 128 Restriction2050_1_checked index (by omega) (by omega)
  else
    if cut : index < 1049984 then
      exact segment_sound _ 1049856 128 Restriction2050_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1049984 128 Restriction2050_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
