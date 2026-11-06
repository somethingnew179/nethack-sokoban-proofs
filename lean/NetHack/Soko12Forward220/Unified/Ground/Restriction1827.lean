import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1827_0_checked : (List.range' 935424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1827_1_checked : (List.range' 935552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1827_2_checked : (List.range' 935680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1827_3_checked : (List.range' 935808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1827_range (index : Nat) (lower : 935424 ≤ index) (upper : index < 935936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 935680 then
    if cut : index < 935552 then
      exact segment_sound _ 935424 128 Restriction1827_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 935552 128 Restriction1827_1_checked index (by omega) (by omega)
  else
    if cut : index < 935808 then
      exact segment_sound _ 935680 128 Restriction1827_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 935808 128 Restriction1827_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
