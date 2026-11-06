import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2364_0_checked : (List.range' 1210368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2364_1_checked : (List.range' 1210496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2364_2_checked : (List.range' 1210624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2364_3_checked : (List.range' 1210752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2364_range (index : Nat) (lower : 1210368 ≤ index) (upper : index < 1210880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1210624 then
    if cut : index < 1210496 then
      exact segment_sound _ 1210368 128 Restriction2364_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1210496 128 Restriction2364_1_checked index (by omega) (by omega)
  else
    if cut : index < 1210752 then
      exact segment_sound _ 1210624 128 Restriction2364_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1210752 128 Restriction2364_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
