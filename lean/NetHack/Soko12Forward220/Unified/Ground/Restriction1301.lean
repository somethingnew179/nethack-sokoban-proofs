import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1301_0_checked : (List.range' 666112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1301_1_checked : (List.range' 666240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1301_2_checked : (List.range' 666368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1301_3_checked : (List.range' 666496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1301_range (index : Nat) (lower : 666112 ≤ index) (upper : index < 666624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 666368 then
    if cut : index < 666240 then
      exact segment_sound _ 666112 128 Restriction1301_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 666240 128 Restriction1301_1_checked index (by omega) (by omega)
  else
    if cut : index < 666496 then
      exact segment_sound _ 666368 128 Restriction1301_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 666496 128 Restriction1301_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
