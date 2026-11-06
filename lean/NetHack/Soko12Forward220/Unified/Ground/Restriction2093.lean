import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2093_0_checked : (List.range' 1071616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2093_1_checked : (List.range' 1071744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2093_2_checked : (List.range' 1071872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2093_3_checked : (List.range' 1072000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2093_range (index : Nat) (lower : 1071616 ≤ index) (upper : index < 1072128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1071872 then
    if cut : index < 1071744 then
      exact segment_sound _ 1071616 128 Restriction2093_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1071744 128 Restriction2093_1_checked index (by omega) (by omega)
  else
    if cut : index < 1072000 then
      exact segment_sound _ 1071872 128 Restriction2093_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1072000 128 Restriction2093_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
