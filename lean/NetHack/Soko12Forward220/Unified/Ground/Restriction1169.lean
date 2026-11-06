import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1169_0_checked : (List.range' 598528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1169_1_checked : (List.range' 598656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1169_2_checked : (List.range' 598784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1169_3_checked : (List.range' 598912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1169_range (index : Nat) (lower : 598528 ≤ index) (upper : index < 599040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 598784 then
    if cut : index < 598656 then
      exact segment_sound _ 598528 128 Restriction1169_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 598656 128 Restriction1169_1_checked index (by omega) (by omega)
  else
    if cut : index < 598912 then
      exact segment_sound _ 598784 128 Restriction1169_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 598912 128 Restriction1169_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
