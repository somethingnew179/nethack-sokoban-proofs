import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1826_0_checked : (List.range' 934912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1826_1_checked : (List.range' 935040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1826_2_checked : (List.range' 935168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1826_3_checked : (List.range' 935296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1826_range (index : Nat) (lower : 934912 ≤ index) (upper : index < 935424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 935168 then
    if cut : index < 935040 then
      exact segment_sound _ 934912 128 Restriction1826_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 935040 128 Restriction1826_1_checked index (by omega) (by omega)
  else
    if cut : index < 935296 then
      exact segment_sound _ 935168 128 Restriction1826_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 935296 128 Restriction1826_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
