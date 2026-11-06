import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2546_0_checked : (List.range' 1303552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2546_1_checked : (List.range' 1303680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2546_2_checked : (List.range' 1303808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2546_3_checked : (List.range' 1303936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2546_range (index : Nat) (lower : 1303552 ≤ index) (upper : index < 1304064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1303808 then
    if cut : index < 1303680 then
      exact segment_sound _ 1303552 128 Restriction2546_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1303680 128 Restriction2546_1_checked index (by omega) (by omega)
  else
    if cut : index < 1303936 then
      exact segment_sound _ 1303808 128 Restriction2546_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1303936 128 Restriction2546_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
