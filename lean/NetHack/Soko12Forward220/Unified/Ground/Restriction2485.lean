import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2485_0_checked : (List.range' 1272320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2485_1_checked : (List.range' 1272448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2485_2_checked : (List.range' 1272576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2485_3_checked : (List.range' 1272704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2485_range (index : Nat) (lower : 1272320 ≤ index) (upper : index < 1272832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1272576 then
    if cut : index < 1272448 then
      exact segment_sound _ 1272320 128 Restriction2485_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1272448 128 Restriction2485_1_checked index (by omega) (by omega)
  else
    if cut : index < 1272704 then
      exact segment_sound _ 1272576 128 Restriction2485_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1272704 128 Restriction2485_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
