import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1853_0_checked : (List.range' 948736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1853_1_checked : (List.range' 948864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1853_2_checked : (List.range' 948992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1853_3_checked : (List.range' 949120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1853_range (index : Nat) (lower : 948736 ≤ index) (upper : index < 949248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 948992 then
    if cut : index < 948864 then
      exact segment_sound _ 948736 128 Restriction1853_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 948864 128 Restriction1853_1_checked index (by omega) (by omega)
  else
    if cut : index < 949120 then
      exact segment_sound _ 948992 128 Restriction1853_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 949120 128 Restriction1853_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
