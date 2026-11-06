import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2614_0_checked : (List.range' 1338368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2614_1_checked : (List.range' 1338496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2614_2_checked : (List.range' 1338624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2614_3_checked : (List.range' 1338752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2614_range (index : Nat) (lower : 1338368 ≤ index) (upper : index < 1338880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1338624 then
    if cut : index < 1338496 then
      exact segment_sound _ 1338368 128 Restriction2614_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1338496 128 Restriction2614_1_checked index (by omega) (by omega)
  else
    if cut : index < 1338752 then
      exact segment_sound _ 1338624 128 Restriction2614_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1338752 128 Restriction2614_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
