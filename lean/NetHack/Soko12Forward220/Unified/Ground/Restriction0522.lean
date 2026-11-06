import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0522_0_checked : (List.range' 267264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0522_1_checked : (List.range' 267392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0522_2_checked : (List.range' 267520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0522_3_checked : (List.range' 267648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0522_range (index : Nat) (lower : 267264 ≤ index) (upper : index < 267776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 267520 then
    if cut : index < 267392 then
      exact segment_sound _ 267264 128 Restriction0522_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 267392 128 Restriction0522_1_checked index (by omega) (by omega)
  else
    if cut : index < 267648 then
      exact segment_sound _ 267520 128 Restriction0522_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 267648 128 Restriction0522_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
