import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1053_0_checked : (List.range' 539136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1053_1_checked : (List.range' 539264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1053_2_checked : (List.range' 539392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1053_3_checked : (List.range' 539520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1053_range (index : Nat) (lower : 539136 ≤ index) (upper : index < 539648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 539392 then
    if cut : index < 539264 then
      exact segment_sound _ 539136 128 Restriction1053_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 539264 128 Restriction1053_1_checked index (by omega) (by omega)
  else
    if cut : index < 539520 then
      exact segment_sound _ 539392 128 Restriction1053_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 539520 128 Restriction1053_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
