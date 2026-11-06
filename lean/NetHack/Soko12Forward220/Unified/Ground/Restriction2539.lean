import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2539_0_checked : (List.range' 1299968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2539_1_checked : (List.range' 1300096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2539_2_checked : (List.range' 1300224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2539_3_checked : (List.range' 1300352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2539_range (index : Nat) (lower : 1299968 ≤ index) (upper : index < 1300480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1300224 then
    if cut : index < 1300096 then
      exact segment_sound _ 1299968 128 Restriction2539_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1300096 128 Restriction2539_1_checked index (by omega) (by omega)
  else
    if cut : index < 1300352 then
      exact segment_sound _ 1300224 128 Restriction2539_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1300352 128 Restriction2539_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
