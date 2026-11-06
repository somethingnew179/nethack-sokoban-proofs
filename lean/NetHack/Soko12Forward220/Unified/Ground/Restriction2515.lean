import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2515_0_checked : (List.range' 1287680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2515_1_checked : (List.range' 1287808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2515_2_checked : (List.range' 1287936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2515_3_checked : (List.range' 1288064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2515_range (index : Nat) (lower : 1287680 ≤ index) (upper : index < 1288192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1287936 then
    if cut : index < 1287808 then
      exact segment_sound _ 1287680 128 Restriction2515_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1287808 128 Restriction2515_1_checked index (by omega) (by omega)
  else
    if cut : index < 1288064 then
      exact segment_sound _ 1287936 128 Restriction2515_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1288064 128 Restriction2515_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
