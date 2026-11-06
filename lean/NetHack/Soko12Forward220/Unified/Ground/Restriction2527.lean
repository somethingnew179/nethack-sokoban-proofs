import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2527_0_checked : (List.range' 1293824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2527_1_checked : (List.range' 1293952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2527_2_checked : (List.range' 1294080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2527_3_checked : (List.range' 1294208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2527_range (index : Nat) (lower : 1293824 ≤ index) (upper : index < 1294336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1294080 then
    if cut : index < 1293952 then
      exact segment_sound _ 1293824 128 Restriction2527_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1293952 128 Restriction2527_1_checked index (by omega) (by omega)
  else
    if cut : index < 1294208 then
      exact segment_sound _ 1294080 128 Restriction2527_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1294208 128 Restriction2527_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
