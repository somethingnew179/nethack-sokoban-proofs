import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1892_0_checked : (List.range' 968704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1892_1_checked : (List.range' 968832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1892_2_checked : (List.range' 968960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1892_3_checked : (List.range' 969088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1892_range (index : Nat) (lower : 968704 ≤ index) (upper : index < 969216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 968960 then
    if cut : index < 968832 then
      exact segment_sound _ 968704 128 Restriction1892_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 968832 128 Restriction1892_1_checked index (by omega) (by omega)
  else
    if cut : index < 969088 then
      exact segment_sound _ 968960 128 Restriction1892_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 969088 128 Restriction1892_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
