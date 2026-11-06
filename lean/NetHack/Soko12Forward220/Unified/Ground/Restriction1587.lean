import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1587_0_checked : (List.range' 812544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1587_1_checked : (List.range' 812672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1587_2_checked : (List.range' 812800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1587_3_checked : (List.range' 812928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1587_range (index : Nat) (lower : 812544 ≤ index) (upper : index < 813056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 812800 then
    if cut : index < 812672 then
      exact segment_sound _ 812544 128 Restriction1587_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 812672 128 Restriction1587_1_checked index (by omega) (by omega)
  else
    if cut : index < 812928 then
      exact segment_sound _ 812800 128 Restriction1587_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 812928 128 Restriction1587_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
