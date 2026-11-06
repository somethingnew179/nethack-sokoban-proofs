import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2377_0_checked : (List.range' 1217024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2377_1_checked : (List.range' 1217152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2377_2_checked : (List.range' 1217280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2377_3_checked : (List.range' 1217408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2377_range (index : Nat) (lower : 1217024 ≤ index) (upper : index < 1217536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1217280 then
    if cut : index < 1217152 then
      exact segment_sound _ 1217024 128 Restriction2377_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1217152 128 Restriction2377_1_checked index (by omega) (by omega)
  else
    if cut : index < 1217408 then
      exact segment_sound _ 1217280 128 Restriction2377_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1217408 128 Restriction2377_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
