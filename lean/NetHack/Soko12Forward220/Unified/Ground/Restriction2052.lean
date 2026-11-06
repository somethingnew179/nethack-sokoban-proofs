import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2052_0_checked : (List.range' 1050624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2052_1_checked : (List.range' 1050752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2052_2_checked : (List.range' 1050880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2052_3_checked : (List.range' 1051008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2052_range (index : Nat) (lower : 1050624 ≤ index) (upper : index < 1051136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1050880 then
    if cut : index < 1050752 then
      exact segment_sound _ 1050624 128 Restriction2052_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1050752 128 Restriction2052_1_checked index (by omega) (by omega)
  else
    if cut : index < 1051008 then
      exact segment_sound _ 1050880 128 Restriction2052_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1051008 128 Restriction2052_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
