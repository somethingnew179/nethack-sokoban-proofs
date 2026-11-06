import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0639_0_checked : (List.range' 327168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0639_1_checked : (List.range' 327296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0639_2_checked : (List.range' 327424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0639_3_checked : (List.range' 327552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0639_range (index : Nat) (lower : 327168 ≤ index) (upper : index < 327680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 327424 then
    if cut : index < 327296 then
      exact segment_sound _ 327168 128 Restriction0639_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 327296 128 Restriction0639_1_checked index (by omega) (by omega)
  else
    if cut : index < 327552 then
      exact segment_sound _ 327424 128 Restriction0639_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 327552 128 Restriction0639_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
