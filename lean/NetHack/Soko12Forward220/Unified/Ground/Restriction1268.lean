import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1268_0_checked : (List.range' 649216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1268_1_checked : (List.range' 649344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1268_2_checked : (List.range' 649472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1268_3_checked : (List.range' 649600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1268_range (index : Nat) (lower : 649216 ≤ index) (upper : index < 649728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 649472 then
    if cut : index < 649344 then
      exact segment_sound _ 649216 128 Restriction1268_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 649344 128 Restriction1268_1_checked index (by omega) (by omega)
  else
    if cut : index < 649600 then
      exact segment_sound _ 649472 128 Restriction1268_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 649600 128 Restriction1268_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
