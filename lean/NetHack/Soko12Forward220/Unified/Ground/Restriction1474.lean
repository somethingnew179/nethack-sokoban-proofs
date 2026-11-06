import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1474_0_checked : (List.range' 754688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1474_1_checked : (List.range' 754816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1474_2_checked : (List.range' 754944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1474_3_checked : (List.range' 755072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1474_range (index : Nat) (lower : 754688 ≤ index) (upper : index < 755200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 754944 then
    if cut : index < 754816 then
      exact segment_sound _ 754688 128 Restriction1474_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 754816 128 Restriction1474_1_checked index (by omega) (by omega)
  else
    if cut : index < 755072 then
      exact segment_sound _ 754944 128 Restriction1474_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 755072 128 Restriction1474_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
