import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1910_0_checked : (List.range' 977920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1910_1_checked : (List.range' 978048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1910_2_checked : (List.range' 978176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1910_3_checked : (List.range' 978304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1910_range (index : Nat) (lower : 977920 ≤ index) (upper : index < 978432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 978176 then
    if cut : index < 978048 then
      exact segment_sound _ 977920 128 Restriction1910_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 978048 128 Restriction1910_1_checked index (by omega) (by omega)
  else
    if cut : index < 978304 then
      exact segment_sound _ 978176 128 Restriction1910_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 978304 128 Restriction1910_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
