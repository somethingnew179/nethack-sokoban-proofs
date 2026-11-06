import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1662_0_checked : (List.range' 850944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1662_1_checked : (List.range' 851072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1662_2_checked : (List.range' 851200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1662_3_checked : (List.range' 851328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1662_range (index : Nat) (lower : 850944 ≤ index) (upper : index < 851456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 851200 then
    if cut : index < 851072 then
      exact segment_sound _ 850944 128 Restriction1662_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 851072 128 Restriction1662_1_checked index (by omega) (by omega)
  else
    if cut : index < 851328 then
      exact segment_sound _ 851200 128 Restriction1662_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 851328 128 Restriction1662_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
