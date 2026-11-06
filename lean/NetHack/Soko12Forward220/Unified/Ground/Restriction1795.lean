import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1795_0_checked : (List.range' 919040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1795_1_checked : (List.range' 919168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1795_2_checked : (List.range' 919296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1795_3_checked : (List.range' 919424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1795_range (index : Nat) (lower : 919040 ≤ index) (upper : index < 919552) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 919296 then
    if cut : index < 919168 then
      exact segment_sound _ 919040 128 Restriction1795_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 919168 128 Restriction1795_1_checked index (by omega) (by omega)
  else
    if cut : index < 919424 then
      exact segment_sound _ 919296 128 Restriction1795_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 919424 128 Restriction1795_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
