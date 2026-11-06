import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0296_0_checked : (List.range' 151552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0296_1_checked : (List.range' 151680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0296_2_checked : (List.range' 151808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0296_3_checked : (List.range' 151936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0296_range (index : Nat) (lower : 151552 ≤ index) (upper : index < 152064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 151808 then
    if cut : index < 151680 then
      exact segment_sound _ 151552 128 Restriction0296_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151680 128 Restriction0296_1_checked index (by omega) (by omega)
  else
    if cut : index < 151936 then
      exact segment_sound _ 151808 128 Restriction0296_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151936 128 Restriction0296_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
