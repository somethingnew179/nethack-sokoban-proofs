import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0474_0_checked : (List.range' 242688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0474_1_checked : (List.range' 242816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0474_2_checked : (List.range' 242944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0474_3_checked : (List.range' 243072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0474_range (index : Nat) (lower : 242688 ≤ index) (upper : index < 243200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 242944 then
    if cut : index < 242816 then
      exact segment_sound _ 242688 128 Restriction0474_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 242816 128 Restriction0474_1_checked index (by omega) (by omega)
  else
    if cut : index < 243072 then
      exact segment_sound _ 242944 128 Restriction0474_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 243072 128 Restriction0474_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
