import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2070_0_checked : (List.range' 1059840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2070_1_checked : (List.range' 1059968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2070_2_checked : (List.range' 1060096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2070_3_checked : (List.range' 1060224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2070_range (index : Nat) (lower : 1059840 ≤ index) (upper : index < 1060352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1060096 then
    if cut : index < 1059968 then
      exact segment_sound _ 1059840 128 Restriction2070_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1059968 128 Restriction2070_1_checked index (by omega) (by omega)
  else
    if cut : index < 1060224 then
      exact segment_sound _ 1060096 128 Restriction2070_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1060224 128 Restriction2070_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
