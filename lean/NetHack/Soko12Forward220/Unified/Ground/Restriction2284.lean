import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2284_0_checked : (List.range' 1169408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2284_1_checked : (List.range' 1169536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2284_2_checked : (List.range' 1169664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2284_3_checked : (List.range' 1169792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2284_range (index : Nat) (lower : 1169408 ≤ index) (upper : index < 1169920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1169664 then
    if cut : index < 1169536 then
      exact segment_sound _ 1169408 128 Restriction2284_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1169536 128 Restriction2284_1_checked index (by omega) (by omega)
  else
    if cut : index < 1169792 then
      exact segment_sound _ 1169664 128 Restriction2284_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1169792 128 Restriction2284_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
