import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2301_0_checked : (List.range' 1178112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2301_1_checked : (List.range' 1178240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2301_2_checked : (List.range' 1178368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2301_3_checked : (List.range' 1178496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2301_range (index : Nat) (lower : 1178112 ≤ index) (upper : index < 1178624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1178368 then
    if cut : index < 1178240 then
      exact segment_sound _ 1178112 128 Restriction2301_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1178240 128 Restriction2301_1_checked index (by omega) (by omega)
  else
    if cut : index < 1178496 then
      exact segment_sound _ 1178368 128 Restriction2301_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1178496 128 Restriction2301_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
