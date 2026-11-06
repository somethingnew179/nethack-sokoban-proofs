import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1327_0_checked : (List.range' 679424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1327_1_checked : (List.range' 679552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1327_2_checked : (List.range' 679680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1327_3_checked : (List.range' 679808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1327_range (index : Nat) (lower : 679424 ≤ index) (upper : index < 679936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 679680 then
    if cut : index < 679552 then
      exact segment_sound _ 679424 128 Restriction1327_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 679552 128 Restriction1327_1_checked index (by omega) (by omega)
  else
    if cut : index < 679808 then
      exact segment_sound _ 679680 128 Restriction1327_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 679808 128 Restriction1327_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
