import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2012_0_checked : (List.range' 1030144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2012_1_checked : (List.range' 1030272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2012_2_checked : (List.range' 1030400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2012_3_checked : (List.range' 1030528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2012_range (index : Nat) (lower : 1030144 ≤ index) (upper : index < 1030656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1030400 then
    if cut : index < 1030272 then
      exact segment_sound _ 1030144 128 Restriction2012_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1030272 128 Restriction2012_1_checked index (by omega) (by omega)
  else
    if cut : index < 1030528 then
      exact segment_sound _ 1030400 128 Restriction2012_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1030528 128 Restriction2012_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
