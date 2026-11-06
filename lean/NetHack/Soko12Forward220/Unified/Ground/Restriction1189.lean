import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1189_0_checked : (List.range' 608768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1189_1_checked : (List.range' 608896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1189_2_checked : (List.range' 609024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1189_3_checked : (List.range' 609152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1189_range (index : Nat) (lower : 608768 ≤ index) (upper : index < 609280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 609024 then
    if cut : index < 608896 then
      exact segment_sound _ 608768 128 Restriction1189_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 608896 128 Restriction1189_1_checked index (by omega) (by omega)
  else
    if cut : index < 609152 then
      exact segment_sound _ 609024 128 Restriction1189_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 609152 128 Restriction1189_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
