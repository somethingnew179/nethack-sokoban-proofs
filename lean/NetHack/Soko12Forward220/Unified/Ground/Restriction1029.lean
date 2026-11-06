import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1029_0_checked : (List.range' 526848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1029_1_checked : (List.range' 526976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1029_2_checked : (List.range' 527104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1029_3_checked : (List.range' 527232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1029_range (index : Nat) (lower : 526848 ≤ index) (upper : index < 527360) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 527104 then
    if cut : index < 526976 then
      exact segment_sound _ 526848 128 Restriction1029_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 526976 128 Restriction1029_1_checked index (by omega) (by omega)
  else
    if cut : index < 527232 then
      exact segment_sound _ 527104 128 Restriction1029_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 527232 128 Restriction1029_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
