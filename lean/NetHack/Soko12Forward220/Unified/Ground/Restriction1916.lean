import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1916_0_checked : (List.range' 980992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1916_1_checked : (List.range' 981120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1916_2_checked : (List.range' 981248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1916_3_checked : (List.range' 981376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1916_range (index : Nat) (lower : 980992 ≤ index) (upper : index < 981504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 981248 then
    if cut : index < 981120 then
      exact segment_sound _ 980992 128 Restriction1916_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 981120 128 Restriction1916_1_checked index (by omega) (by omega)
  else
    if cut : index < 981376 then
      exact segment_sound _ 981248 128 Restriction1916_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 981376 128 Restriction1916_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
