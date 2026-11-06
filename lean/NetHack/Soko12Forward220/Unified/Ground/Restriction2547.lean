import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2547_0_checked : (List.range' 1304064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2547_1_checked : (List.range' 1304192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2547_2_checked : (List.range' 1304320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2547_3_checked : (List.range' 1304448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2547_range (index : Nat) (lower : 1304064 ≤ index) (upper : index < 1304576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1304320 then
    if cut : index < 1304192 then
      exact segment_sound _ 1304064 128 Restriction2547_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1304192 128 Restriction2547_1_checked index (by omega) (by omega)
  else
    if cut : index < 1304448 then
      exact segment_sound _ 1304320 128 Restriction2547_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1304448 128 Restriction2547_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
