import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1684_0_checked : (List.range' 862208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1684_1_checked : (List.range' 862336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1684_2_checked : (List.range' 862464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1684_3_checked : (List.range' 862592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1684_range (index : Nat) (lower : 862208 ≤ index) (upper : index < 862720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 862464 then
    if cut : index < 862336 then
      exact segment_sound _ 862208 128 Restriction1684_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 862336 128 Restriction1684_1_checked index (by omega) (by omega)
  else
    if cut : index < 862592 then
      exact segment_sound _ 862464 128 Restriction1684_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 862592 128 Restriction1684_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
