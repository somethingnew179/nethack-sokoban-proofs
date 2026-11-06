import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2180_0_checked : (List.range' 1116160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2180_1_checked : (List.range' 1116288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2180_2_checked : (List.range' 1116416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2180_3_checked : (List.range' 1116544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2180_range (index : Nat) (lower : 1116160 ≤ index) (upper : index < 1116672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1116416 then
    if cut : index < 1116288 then
      exact segment_sound _ 1116160 128 Restriction2180_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1116288 128 Restriction2180_1_checked index (by omega) (by omega)
  else
    if cut : index < 1116544 then
      exact segment_sound _ 1116416 128 Restriction2180_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1116544 128 Restriction2180_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
