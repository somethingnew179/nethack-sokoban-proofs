import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1992_0_checked : (List.range' 1019904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1992_1_checked : (List.range' 1020032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1992_2_checked : (List.range' 1020160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1992_3_checked : (List.range' 1020288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1992_range (index : Nat) (lower : 1019904 ≤ index) (upper : index < 1020416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1020160 then
    if cut : index < 1020032 then
      exact segment_sound _ 1019904 128 Restriction1992_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1020032 128 Restriction1992_1_checked index (by omega) (by omega)
  else
    if cut : index < 1020288 then
      exact segment_sound _ 1020160 128 Restriction1992_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1020288 128 Restriction1992_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
