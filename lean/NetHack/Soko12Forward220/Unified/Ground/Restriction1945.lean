import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1945_0_checked : (List.range' 995840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1945_1_checked : (List.range' 995968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1945_2_checked : (List.range' 996096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1945_3_checked : (List.range' 996224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1945_range (index : Nat) (lower : 995840 ≤ index) (upper : index < 996352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 996096 then
    if cut : index < 995968 then
      exact segment_sound _ 995840 128 Restriction1945_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 995968 128 Restriction1945_1_checked index (by omega) (by omega)
  else
    if cut : index < 996224 then
      exact segment_sound _ 996096 128 Restriction1945_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 996224 128 Restriction1945_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
