import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2009_0_checked : (List.range' 1028608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2009_1_checked : (List.range' 1028736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2009_2_checked : (List.range' 1028864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2009_3_checked : (List.range' 1028992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2009_range (index : Nat) (lower : 1028608 ≤ index) (upper : index < 1029120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1028864 then
    if cut : index < 1028736 then
      exact segment_sound _ 1028608 128 Restriction2009_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1028736 128 Restriction2009_1_checked index (by omega) (by omega)
  else
    if cut : index < 1028992 then
      exact segment_sound _ 1028864 128 Restriction2009_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1028992 128 Restriction2009_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
