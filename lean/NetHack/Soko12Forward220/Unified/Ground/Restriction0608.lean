import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0608_0_checked : (List.range' 311296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0608_1_checked : (List.range' 311424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0608_2_checked : (List.range' 311552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0608_3_checked : (List.range' 311680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0608_range (index : Nat) (lower : 311296 ≤ index) (upper : index < 311808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 311552 then
    if cut : index < 311424 then
      exact segment_sound _ 311296 128 Restriction0608_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 311424 128 Restriction0608_1_checked index (by omega) (by omega)
  else
    if cut : index < 311680 then
      exact segment_sound _ 311552 128 Restriction0608_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 311680 128 Restriction0608_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
