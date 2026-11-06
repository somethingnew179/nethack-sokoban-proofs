import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0653_0_checked : (List.range' 334336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0653_1_checked : (List.range' 334464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0653_2_checked : (List.range' 334592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0653_3_checked : (List.range' 334720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0653_range (index : Nat) (lower : 334336 ≤ index) (upper : index < 334848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 334592 then
    if cut : index < 334464 then
      exact segment_sound _ 334336 128 Restriction0653_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 334464 128 Restriction0653_1_checked index (by omega) (by omega)
  else
    if cut : index < 334720 then
      exact segment_sound _ 334592 128 Restriction0653_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 334720 128 Restriction0653_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
