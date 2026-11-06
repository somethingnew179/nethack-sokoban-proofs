import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1384_0_checked : (List.range' 708608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1384_1_checked : (List.range' 708736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1384_2_checked : (List.range' 708864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1384_3_checked : (List.range' 708992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1384_range (index : Nat) (lower : 708608 ≤ index) (upper : index < 709120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 708864 then
    if cut : index < 708736 then
      exact segment_sound _ 708608 128 Restriction1384_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 708736 128 Restriction1384_1_checked index (by omega) (by omega)
  else
    if cut : index < 708992 then
      exact segment_sound _ 708864 128 Restriction1384_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 708992 128 Restriction1384_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
