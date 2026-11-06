import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0837_0_checked : (List.range' 428544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0837_1_checked : (List.range' 428672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0837_2_checked : (List.range' 428800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0837_3_checked : (List.range' 428928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0837_range (index : Nat) (lower : 428544 ≤ index) (upper : index < 429056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 428800 then
    if cut : index < 428672 then
      exact segment_sound _ 428544 128 Restriction0837_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 428672 128 Restriction0837_1_checked index (by omega) (by omega)
  else
    if cut : index < 428928 then
      exact segment_sound _ 428800 128 Restriction0837_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 428928 128 Restriction0837_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
