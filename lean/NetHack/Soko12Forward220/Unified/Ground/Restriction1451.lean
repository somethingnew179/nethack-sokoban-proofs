import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1451_0_checked : (List.range' 742912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1451_1_checked : (List.range' 743040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1451_2_checked : (List.range' 743168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1451_3_checked : (List.range' 743296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1451_range (index : Nat) (lower : 742912 ≤ index) (upper : index < 743424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 743168 then
    if cut : index < 743040 then
      exact segment_sound _ 742912 128 Restriction1451_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 743040 128 Restriction1451_1_checked index (by omega) (by omega)
  else
    if cut : index < 743296 then
      exact segment_sound _ 743168 128 Restriction1451_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 743296 128 Restriction1451_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
