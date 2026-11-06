import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0076_0_checked : (List.range' 38912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0076_1_checked : (List.range' 39040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0076_2_checked : (List.range' 39168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0076_3_checked : (List.range' 39296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0076_range (index : Nat) (lower : 38912 ≤ index) (upper : index < 39424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 39168 then
    if cut : index < 39040 then
      exact segment_sound _ 38912 128 Restriction0076_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39040 128 Restriction0076_1_checked index (by omega) (by omega)
  else
    if cut : index < 39296 then
      exact segment_sound _ 39168 128 Restriction0076_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39296 128 Restriction0076_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
