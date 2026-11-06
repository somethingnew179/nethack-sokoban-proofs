import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2247_0_checked : (List.range' 1150464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2247_1_checked : (List.range' 1150592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2247_2_checked : (List.range' 1150720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2247_3_checked : (List.range' 1150848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2247_range (index : Nat) (lower : 1150464 ≤ index) (upper : index < 1150976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1150720 then
    if cut : index < 1150592 then
      exact segment_sound _ 1150464 128 Restriction2247_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1150592 128 Restriction2247_1_checked index (by omega) (by omega)
  else
    if cut : index < 1150848 then
      exact segment_sound _ 1150720 128 Restriction2247_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1150848 128 Restriction2247_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
