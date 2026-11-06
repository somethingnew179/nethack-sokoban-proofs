import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1924_0_checked : (List.range' 985088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1924_1_checked : (List.range' 985216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1924_2_checked : (List.range' 985344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1924_3_checked : (List.range' 985472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1924_range (index : Nat) (lower : 985088 ≤ index) (upper : index < 985600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 985344 then
    if cut : index < 985216 then
      exact segment_sound _ 985088 128 Restriction1924_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 985216 128 Restriction1924_1_checked index (by omega) (by omega)
  else
    if cut : index < 985472 then
      exact segment_sound _ 985344 128 Restriction1924_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 985472 128 Restriction1924_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
