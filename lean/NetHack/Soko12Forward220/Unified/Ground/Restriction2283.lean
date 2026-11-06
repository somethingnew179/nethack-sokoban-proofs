import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2283_0_checked : (List.range' 1168896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2283_1_checked : (List.range' 1169024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2283_2_checked : (List.range' 1169152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2283_3_checked : (List.range' 1169280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2283_range (index : Nat) (lower : 1168896 ≤ index) (upper : index < 1169408) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1169152 then
    if cut : index < 1169024 then
      exact segment_sound _ 1168896 128 Restriction2283_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1169024 128 Restriction2283_1_checked index (by omega) (by omega)
  else
    if cut : index < 1169280 then
      exact segment_sound _ 1169152 128 Restriction2283_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1169280 128 Restriction2283_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
