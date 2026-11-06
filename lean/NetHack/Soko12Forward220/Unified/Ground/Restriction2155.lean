import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2155_0_checked : (List.range' 1103360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2155_1_checked : (List.range' 1103488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2155_2_checked : (List.range' 1103616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2155_3_checked : (List.range' 1103744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2155_range (index : Nat) (lower : 1103360 ≤ index) (upper : index < 1103872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1103616 then
    if cut : index < 1103488 then
      exact segment_sound _ 1103360 128 Restriction2155_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1103488 128 Restriction2155_1_checked index (by omega) (by omega)
  else
    if cut : index < 1103744 then
      exact segment_sound _ 1103616 128 Restriction2155_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1103744 128 Restriction2155_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
