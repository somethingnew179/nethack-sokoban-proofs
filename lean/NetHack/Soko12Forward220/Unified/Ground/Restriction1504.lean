import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1504_0_checked : (List.range' 770048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1504_1_checked : (List.range' 770176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1504_2_checked : (List.range' 770304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1504_3_checked : (List.range' 770432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1504_range (index : Nat) (lower : 770048 ≤ index) (upper : index < 770560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 770304 then
    if cut : index < 770176 then
      exact segment_sound _ 770048 128 Restriction1504_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 770176 128 Restriction1504_1_checked index (by omega) (by omega)
  else
    if cut : index < 770432 then
      exact segment_sound _ 770304 128 Restriction1504_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 770432 128 Restriction1504_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
