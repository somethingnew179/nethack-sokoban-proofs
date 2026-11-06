import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1310_0_checked : (List.range' 670720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1310_1_checked : (List.range' 670848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1310_2_checked : (List.range' 670976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1310_3_checked : (List.range' 671104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1310_range (index : Nat) (lower : 670720 ≤ index) (upper : index < 671232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 670976 then
    if cut : index < 670848 then
      exact segment_sound _ 670720 128 Restriction1310_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 670848 128 Restriction1310_1_checked index (by omega) (by omega)
  else
    if cut : index < 671104 then
      exact segment_sound _ 670976 128 Restriction1310_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 671104 128 Restriction1310_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
