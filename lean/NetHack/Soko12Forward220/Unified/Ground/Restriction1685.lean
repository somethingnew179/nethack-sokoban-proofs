import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1685_0_checked : (List.range' 862720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1685_1_checked : (List.range' 862848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1685_2_checked : (List.range' 862976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1685_3_checked : (List.range' 863104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1685_range (index : Nat) (lower : 862720 ≤ index) (upper : index < 863232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 862976 then
    if cut : index < 862848 then
      exact segment_sound _ 862720 128 Restriction1685_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 862848 128 Restriction1685_1_checked index (by omega) (by omega)
  else
    if cut : index < 863104 then
      exact segment_sound _ 862976 128 Restriction1685_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 863104 128 Restriction1685_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
