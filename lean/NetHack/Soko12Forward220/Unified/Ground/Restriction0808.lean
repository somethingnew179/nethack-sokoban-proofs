import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0808_0_checked : (List.range' 413696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0808_1_checked : (List.range' 413824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0808_2_checked : (List.range' 413952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0808_3_checked : (List.range' 414080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0808_range (index : Nat) (lower : 413696 ≤ index) (upper : index < 414208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 413952 then
    if cut : index < 413824 then
      exact segment_sound _ 413696 128 Restriction0808_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 413824 128 Restriction0808_1_checked index (by omega) (by omega)
  else
    if cut : index < 414080 then
      exact segment_sound _ 413952 128 Restriction0808_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 414080 128 Restriction0808_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
