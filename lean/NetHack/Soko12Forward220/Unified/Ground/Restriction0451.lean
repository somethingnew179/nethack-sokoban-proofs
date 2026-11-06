import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0451_0_checked : (List.range' 230912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0451_1_checked : (List.range' 231040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0451_2_checked : (List.range' 231168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0451_3_checked : (List.range' 231296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0451_range (index : Nat) (lower : 230912 ≤ index) (upper : index < 231424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 231168 then
    if cut : index < 231040 then
      exact segment_sound _ 230912 128 Restriction0451_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231040 128 Restriction0451_1_checked index (by omega) (by omega)
  else
    if cut : index < 231296 then
      exact segment_sound _ 231168 128 Restriction0451_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 231296 128 Restriction0451_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
