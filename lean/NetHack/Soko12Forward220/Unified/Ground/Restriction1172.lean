import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1172_0_checked : (List.range' 600064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1172_1_checked : (List.range' 600192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1172_2_checked : (List.range' 600320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1172_3_checked : (List.range' 600448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1172_range (index : Nat) (lower : 600064 ≤ index) (upper : index < 600576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 600320 then
    if cut : index < 600192 then
      exact segment_sound _ 600064 128 Restriction1172_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 600192 128 Restriction1172_1_checked index (by omega) (by omega)
  else
    if cut : index < 600448 then
      exact segment_sound _ 600320 128 Restriction1172_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 600448 128 Restriction1172_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
