import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1367_0_checked : (List.range' 699904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1367_1_checked : (List.range' 700032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1367_2_checked : (List.range' 700160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1367_3_checked : (List.range' 700288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1367_range (index : Nat) (lower : 699904 ≤ index) (upper : index < 700416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 700160 then
    if cut : index < 700032 then
      exact segment_sound _ 699904 128 Restriction1367_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 700032 128 Restriction1367_1_checked index (by omega) (by omega)
  else
    if cut : index < 700288 then
      exact segment_sound _ 700160 128 Restriction1367_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 700288 128 Restriction1367_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
