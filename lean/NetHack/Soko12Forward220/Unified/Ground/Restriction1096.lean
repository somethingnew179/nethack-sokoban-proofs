import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1096_0_checked : (List.range' 561152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1096_1_checked : (List.range' 561280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1096_2_checked : (List.range' 561408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1096_3_checked : (List.range' 561536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1096_range (index : Nat) (lower : 561152 ≤ index) (upper : index < 561664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 561408 then
    if cut : index < 561280 then
      exact segment_sound _ 561152 128 Restriction1096_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 561280 128 Restriction1096_1_checked index (by omega) (by omega)
  else
    if cut : index < 561536 then
      exact segment_sound _ 561408 128 Restriction1096_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 561536 128 Restriction1096_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
