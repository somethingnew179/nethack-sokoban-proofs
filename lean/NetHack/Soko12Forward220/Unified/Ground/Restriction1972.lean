import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1972_0_checked : (List.range' 1009664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1972_1_checked : (List.range' 1009792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1972_2_checked : (List.range' 1009920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1972_3_checked : (List.range' 1010048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1972_range (index : Nat) (lower : 1009664 ≤ index) (upper : index < 1010176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1009920 then
    if cut : index < 1009792 then
      exact segment_sound _ 1009664 128 Restriction1972_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1009792 128 Restriction1972_1_checked index (by omega) (by omega)
  else
    if cut : index < 1010048 then
      exact segment_sound _ 1009920 128 Restriction1972_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1010048 128 Restriction1972_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
