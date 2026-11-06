import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1908_0_checked : (List.range' 976896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1908_1_checked : (List.range' 977024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1908_2_checked : (List.range' 977152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1908_3_checked : (List.range' 977280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1908_range (index : Nat) (lower : 976896 ≤ index) (upper : index < 977408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 977152 then
    if cut : index < 977024 then
      exact segment_sound _ 976896 128 Restriction1908_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 977024 128 Restriction1908_1_checked index (by omega) (by omega)
  else
    if cut : index < 977280 then
      exact segment_sound _ 977152 128 Restriction1908_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 977280 128 Restriction1908_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
