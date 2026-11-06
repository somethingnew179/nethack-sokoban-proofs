import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2556_0_checked : (List.range' 1308672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2556_1_checked : (List.range' 1308800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2556_2_checked : (List.range' 1308928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2556_3_checked : (List.range' 1309056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2556_range (index : Nat) (lower : 1308672 ≤ index) (upper : index < 1309184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1308928 then
    if cut : index < 1308800 then
      exact segment_sound _ 1308672 128 Restriction2556_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1308800 128 Restriction2556_1_checked index (by omega) (by omega)
  else
    if cut : index < 1309056 then
      exact segment_sound _ 1308928 128 Restriction2556_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1309056 128 Restriction2556_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
