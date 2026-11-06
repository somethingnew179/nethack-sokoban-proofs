import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1289_0_checked : (List.range' 659968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1289_1_checked : (List.range' 660096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1289_2_checked : (List.range' 660224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1289_3_checked : (List.range' 660352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1289_range (index : Nat) (lower : 659968 ≤ index) (upper : index < 660480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 660224 then
    if cut : index < 660096 then
      exact segment_sound _ 659968 128 Restriction1289_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 660096 128 Restriction1289_1_checked index (by omega) (by omega)
  else
    if cut : index < 660352 then
      exact segment_sound _ 660224 128 Restriction1289_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 660352 128 Restriction1289_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
