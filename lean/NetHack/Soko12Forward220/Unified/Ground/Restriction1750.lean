import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1750_0_checked : (List.range' 896000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1750_1_checked : (List.range' 896128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1750_2_checked : (List.range' 896256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1750_3_checked : (List.range' 896384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1750_range (index : Nat) (lower : 896000 ≤ index) (upper : index < 896512) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 896256 then
    if cut : index < 896128 then
      exact segment_sound _ 896000 128 Restriction1750_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 896128 128 Restriction1750_1_checked index (by omega) (by omega)
  else
    if cut : index < 896384 then
      exact segment_sound _ 896256 128 Restriction1750_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 896384 128 Restriction1750_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
