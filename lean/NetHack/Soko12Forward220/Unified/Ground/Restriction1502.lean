import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1502_0_checked : (List.range' 769024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1502_1_checked : (List.range' 769152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1502_2_checked : (List.range' 769280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1502_3_checked : (List.range' 769408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1502_range (index : Nat) (lower : 769024 ≤ index) (upper : index < 769536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 769280 then
    if cut : index < 769152 then
      exact segment_sound _ 769024 128 Restriction1502_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 769152 128 Restriction1502_1_checked index (by omega) (by omega)
  else
    if cut : index < 769408 then
      exact segment_sound _ 769280 128 Restriction1502_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 769408 128 Restriction1502_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
