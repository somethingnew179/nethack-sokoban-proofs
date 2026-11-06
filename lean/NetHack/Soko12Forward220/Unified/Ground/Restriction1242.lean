import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1242_0_checked : (List.range' 635904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1242_1_checked : (List.range' 636032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1242_2_checked : (List.range' 636160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1242_3_checked : (List.range' 636288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1242_range (index : Nat) (lower : 635904 ≤ index) (upper : index < 636416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 636160 then
    if cut : index < 636032 then
      exact segment_sound _ 635904 128 Restriction1242_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 636032 128 Restriction1242_1_checked index (by omega) (by omega)
  else
    if cut : index < 636288 then
      exact segment_sound _ 636160 128 Restriction1242_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 636288 128 Restriction1242_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
