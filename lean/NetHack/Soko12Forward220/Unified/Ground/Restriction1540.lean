import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1540_0_checked : (List.range' 788480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1540_1_checked : (List.range' 788608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1540_2_checked : (List.range' 788736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1540_3_checked : (List.range' 788864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1540_range (index : Nat) (lower : 788480 ≤ index) (upper : index < 788992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 788736 then
    if cut : index < 788608 then
      exact segment_sound _ 788480 128 Restriction1540_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 788608 128 Restriction1540_1_checked index (by omega) (by omega)
  else
    if cut : index < 788864 then
      exact segment_sound _ 788736 128 Restriction1540_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 788864 128 Restriction1540_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
