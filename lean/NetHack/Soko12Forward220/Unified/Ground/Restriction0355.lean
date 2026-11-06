import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0355_0_checked : (List.range' 181760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0355_1_checked : (List.range' 181888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0355_2_checked : (List.range' 182016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0355_3_checked : (List.range' 182144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0355_range (index : Nat) (lower : 181760 ≤ index) (upper : index < 182272) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 182016 then
    if cut : index < 181888 then
      exact segment_sound _ 181760 128 Restriction0355_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 181888 128 Restriction0355_1_checked index (by omega) (by omega)
  else
    if cut : index < 182144 then
      exact segment_sound _ 182016 128 Restriction0355_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 182144 128 Restriction0355_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
