import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1665_0_checked : (List.range' 852480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1665_1_checked : (List.range' 852608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1665_2_checked : (List.range' 852736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1665_3_checked : (List.range' 852864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1665_range (index : Nat) (lower : 852480 ≤ index) (upper : index < 852992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 852736 then
    if cut : index < 852608 then
      exact segment_sound _ 852480 128 Restriction1665_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 852608 128 Restriction1665_1_checked index (by omega) (by omega)
  else
    if cut : index < 852864 then
      exact segment_sound _ 852736 128 Restriction1665_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 852864 128 Restriction1665_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
