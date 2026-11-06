import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1661_0_checked : (List.range' 850432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1661_1_checked : (List.range' 850560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1661_2_checked : (List.range' 850688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1661_3_checked : (List.range' 850816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1661_range (index : Nat) (lower : 850432 ≤ index) (upper : index < 850944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 850688 then
    if cut : index < 850560 then
      exact segment_sound _ 850432 128 Restriction1661_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 850560 128 Restriction1661_1_checked index (by omega) (by omega)
  else
    if cut : index < 850816 then
      exact segment_sound _ 850688 128 Restriction1661_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 850816 128 Restriction1661_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
