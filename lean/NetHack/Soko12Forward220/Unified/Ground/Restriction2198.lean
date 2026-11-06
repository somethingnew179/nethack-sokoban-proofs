import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2198_0_checked : (List.range' 1125376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2198_1_checked : (List.range' 1125504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2198_2_checked : (List.range' 1125632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2198_3_checked : (List.range' 1125760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2198_range (index : Nat) (lower : 1125376 ≤ index) (upper : index < 1125888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1125632 then
    if cut : index < 1125504 then
      exact segment_sound _ 1125376 128 Restriction2198_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1125504 128 Restriction2198_1_checked index (by omega) (by omega)
  else
    if cut : index < 1125760 then
      exact segment_sound _ 1125632 128 Restriction2198_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1125760 128 Restriction2198_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
