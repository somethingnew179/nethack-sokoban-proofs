import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1611_0_checked : (List.range' 824832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1611_1_checked : (List.range' 824960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1611_2_checked : (List.range' 825088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1611_3_checked : (List.range' 825216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1611_range (index : Nat) (lower : 824832 ≤ index) (upper : index < 825344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 825088 then
    if cut : index < 824960 then
      exact segment_sound _ 824832 128 Restriction1611_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 824960 128 Restriction1611_1_checked index (by omega) (by omega)
  else
    if cut : index < 825216 then
      exact segment_sound _ 825088 128 Restriction1611_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 825216 128 Restriction1611_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
