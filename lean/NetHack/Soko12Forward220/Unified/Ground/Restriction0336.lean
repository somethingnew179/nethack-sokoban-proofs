import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0336_0_checked : (List.range' 172032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0336_1_checked : (List.range' 172160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0336_2_checked : (List.range' 172288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0336_3_checked : (List.range' 172416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0336_range (index : Nat) (lower : 172032 ≤ index) (upper : index < 172544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 172288 then
    if cut : index < 172160 then
      exact segment_sound _ 172032 128 Restriction0336_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 172160 128 Restriction0336_1_checked index (by omega) (by omega)
  else
    if cut : index < 172416 then
      exact segment_sound _ 172288 128 Restriction0336_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 172416 128 Restriction0336_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
