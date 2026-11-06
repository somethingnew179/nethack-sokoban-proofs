import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2476_0_checked : (List.range' 1267712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2476_1_checked : (List.range' 1267840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2476_2_checked : (List.range' 1267968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2476_3_checked : (List.range' 1268096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2476_range (index : Nat) (lower : 1267712 ≤ index) (upper : index < 1268224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1267968 then
    if cut : index < 1267840 then
      exact segment_sound _ 1267712 128 Restriction2476_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1267840 128 Restriction2476_1_checked index (by omega) (by omega)
  else
    if cut : index < 1268096 then
      exact segment_sound _ 1267968 128 Restriction2476_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1268096 128 Restriction2476_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
