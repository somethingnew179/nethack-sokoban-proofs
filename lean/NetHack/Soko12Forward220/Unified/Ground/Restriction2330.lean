import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2330_0_checked : (List.range' 1192960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2330_1_checked : (List.range' 1193088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2330_2_checked : (List.range' 1193216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2330_3_checked : (List.range' 1193344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2330_range (index : Nat) (lower : 1192960 ≤ index) (upper : index < 1193472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1193216 then
    if cut : index < 1193088 then
      exact segment_sound _ 1192960 128 Restriction2330_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1193088 128 Restriction2330_1_checked index (by omega) (by omega)
  else
    if cut : index < 1193344 then
      exact segment_sound _ 1193216 128 Restriction2330_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1193344 128 Restriction2330_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
