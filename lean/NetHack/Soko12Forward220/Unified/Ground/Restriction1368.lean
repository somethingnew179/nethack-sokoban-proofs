import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1368_0_checked : (List.range' 700416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1368_1_checked : (List.range' 700544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1368_2_checked : (List.range' 700672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1368_3_checked : (List.range' 700800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1368_range (index : Nat) (lower : 700416 ≤ index) (upper : index < 700928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 700672 then
    if cut : index < 700544 then
      exact segment_sound _ 700416 128 Restriction1368_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 700544 128 Restriction1368_1_checked index (by omega) (by omega)
  else
    if cut : index < 700800 then
      exact segment_sound _ 700672 128 Restriction1368_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 700800 128 Restriction1368_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
