import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2296_0_checked : (List.range' 1175552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2296_1_checked : (List.range' 1175680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2296_2_checked : (List.range' 1175808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2296_3_checked : (List.range' 1175936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2296_range (index : Nat) (lower : 1175552 ≤ index) (upper : index < 1176064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1175808 then
    if cut : index < 1175680 then
      exact segment_sound _ 1175552 128 Restriction2296_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1175680 128 Restriction2296_1_checked index (by omega) (by omega)
  else
    if cut : index < 1175936 then
      exact segment_sound _ 1175808 128 Restriction2296_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1175936 128 Restriction2296_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
