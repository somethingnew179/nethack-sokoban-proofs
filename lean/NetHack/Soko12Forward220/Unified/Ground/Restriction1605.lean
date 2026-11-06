import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1605_0_checked : (List.range' 821760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1605_1_checked : (List.range' 821888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1605_2_checked : (List.range' 822016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1605_3_checked : (List.range' 822144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1605_range (index : Nat) (lower : 821760 ≤ index) (upper : index < 822272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 822016 then
    if cut : index < 821888 then
      exact segment_sound _ 821760 128 Restriction1605_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 821888 128 Restriction1605_1_checked index (by omega) (by omega)
  else
    if cut : index < 822144 then
      exact segment_sound _ 822016 128 Restriction1605_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 822144 128 Restriction1605_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
