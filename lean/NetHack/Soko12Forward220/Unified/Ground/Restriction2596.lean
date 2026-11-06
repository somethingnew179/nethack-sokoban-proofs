import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2596_0_checked : (List.range' 1329152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2596_1_checked : (List.range' 1329280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2596_2_checked : (List.range' 1329408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2596_3_checked : (List.range' 1329536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2596_range (index : Nat) (lower : 1329152 ≤ index) (upper : index < 1329664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1329408 then
    if cut : index < 1329280 then
      exact segment_sound _ 1329152 128 Restriction2596_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1329280 128 Restriction2596_1_checked index (by omega) (by omega)
  else
    if cut : index < 1329536 then
      exact segment_sound _ 1329408 128 Restriction2596_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1329536 128 Restriction2596_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
