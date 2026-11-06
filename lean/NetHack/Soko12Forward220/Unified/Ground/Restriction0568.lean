import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0568_0_checked : (List.range' 290816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0568_1_checked : (List.range' 290944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0568_2_checked : (List.range' 291072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0568_3_checked : (List.range' 291200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0568_range (index : Nat) (lower : 290816 ≤ index) (upper : index < 291328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 291072 then
    if cut : index < 290944 then
      exact segment_sound _ 290816 128 Restriction0568_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 290944 128 Restriction0568_1_checked index (by omega) (by omega)
  else
    if cut : index < 291200 then
      exact segment_sound _ 291072 128 Restriction0568_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291200 128 Restriction0568_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
