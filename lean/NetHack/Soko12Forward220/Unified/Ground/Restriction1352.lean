import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1352_0_checked : (List.range' 692224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1352_1_checked : (List.range' 692352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1352_2_checked : (List.range' 692480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1352_3_checked : (List.range' 692608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1352_range (index : Nat) (lower : 692224 ≤ index) (upper : index < 692736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 692480 then
    if cut : index < 692352 then
      exact segment_sound _ 692224 128 Restriction1352_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 692352 128 Restriction1352_1_checked index (by omega) (by omega)
  else
    if cut : index < 692608 then
      exact segment_sound _ 692480 128 Restriction1352_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 692608 128 Restriction1352_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
