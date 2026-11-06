import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2360_0_checked : (List.range' 1208320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2360_1_checked : (List.range' 1208448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2360_2_checked : (List.range' 1208576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2360_3_checked : (List.range' 1208704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2360_range (index : Nat) (lower : 1208320 ≤ index) (upper : index < 1208832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1208576 then
    if cut : index < 1208448 then
      exact segment_sound _ 1208320 128 Restriction2360_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1208448 128 Restriction2360_1_checked index (by omega) (by omega)
  else
    if cut : index < 1208704 then
      exact segment_sound _ 1208576 128 Restriction2360_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1208704 128 Restriction2360_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
