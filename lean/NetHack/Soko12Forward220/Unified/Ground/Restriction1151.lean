import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1151_0_checked : (List.range' 589312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1151_1_checked : (List.range' 589440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1151_2_checked : (List.range' 589568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1151_3_checked : (List.range' 589696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1151_range (index : Nat) (lower : 589312 ≤ index) (upper : index < 589824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 589568 then
    if cut : index < 589440 then
      exact segment_sound _ 589312 128 Restriction1151_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 589440 128 Restriction1151_1_checked index (by omega) (by omega)
  else
    if cut : index < 589696 then
      exact segment_sound _ 589568 128 Restriction1151_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 589696 128 Restriction1151_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
