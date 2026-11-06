import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2525_0_checked : (List.range' 1292800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2525_1_checked : (List.range' 1292928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2525_2_checked : (List.range' 1293056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2525_3_checked : (List.range' 1293184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2525_range (index : Nat) (lower : 1292800 ≤ index) (upper : index < 1293312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1293056 then
    if cut : index < 1292928 then
      exact segment_sound _ 1292800 128 Restriction2525_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1292928 128 Restriction2525_1_checked index (by omega) (by omega)
  else
    if cut : index < 1293184 then
      exact segment_sound _ 1293056 128 Restriction2525_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1293184 128 Restriction2525_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
