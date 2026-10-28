import Decoupling.HighDim.CohomologyPresentation
import Decoupling.HighDim.ToricSplitLayers
import Decoupling.HighDim.KoszulRegular
import Decoupling.HighDim.LaurentArithmeticData

/-!
# HD012 connecting matrix ranks and box radii to dense input size

An isolated nonzero free term would have free homology. In positive
spatial dimension such a module cannot have augmentation action. Thus
the split-profile assumption, rather than an extra input-size premise,
excludes free ranks invisible to both adjacent differential matrices.
-/
namespace Decoupling.HighDim.AlgorithmInputSize
open CategoryTheory CategoryTheory.Limits Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D q m r : ℕ}

theorem free_augmentation_rank_zero (hD : 0 < D)
    (h : TrivialLayers.AugmentationAction (ModuleCat.of (Laurent K D) (Fin q → Laurent K D))) :
    q = 0 := by
  by_contra hq
  let i : Fin D := ⟨0, hD⟩
  let j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hv := congrFun (h (difference K i) (Pi.single j 1)) j
  have hd : difference K i = 0 := by
    change (difference K i) * (Pi.single j (1 : Laurent K D) : Fin q → Laurent K D) j =
      constant (augmentation (difference K i)) * (Pi.single j (1 : Laurent K D) : Fin q → Laurent K D) j at hv
    simpa using hv
  exact Koszul.difference_ne_zero i hd

theorem isolated_rank_zero (hD : 0 < D)
    (b : Matrix (Fin q) (Fin 0) (Laurent K D))
    (d : Matrix (Fin 0) (Fin q) (Laurent K D)) (hbd : d * b = 0)
    (hH : TrivialLayers.AugmentationAction (CohomologyPresentation.window b d hbd).homology) :
    q = 0 := by
  let S := CohomologyPresentation.window b d hbd
  have hf : S.f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    funext i
    change (b *ᵥ v) i = 0
    simp [Matrix.mulVec, dotProduct]
  have hg : S.g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    funext i
    exact Fin.elim0 i
  have e : S.homology ≅ S.X₂ := (ShortComplex.HomologyData.ofZeros S hf hg).left.homologyIso
  exact free_augmentation_rank_zero hD (TrivialLayers.augmentationAction_of_iso e.symm hH)

theorem adjacent_rank_bound (hD : 0 < D)
    (b : Matrix (Fin q) (Fin m) (Laurent K D))
    (d : Matrix (Fin r) (Fin q) (Laurent K D)) (hbd : d * b = 0)
    (hH : TrivialLayers.AugmentationAction (CohomologyPresentation.window b d hbd).homology) :
    q ≤ m * q + q * r := by
  by_cases hm : m = 0
  · subst m
    by_cases hr : r = 0
    · subst r
      rw [isolated_rank_zero hD b d hbd hH]
    · have hrp : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
      nlinarith
  · have hmp : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    nlinarith

/-- For a nonempty differential coefficient array, the common radius is
bounded by the actual dense coefficient count, in every positive D. -/
theorem radius_le_dense_size (D h entries : ℕ) (hD : 0 < D) (he : 0 < entries) :
    h ≤ entries * LaurentArithmetic.boxSize D h := by
  have hbase : 1 ≤ 2 * h + 1 := by omega
  have hp : 2 * h + 1 ≤ (2 * h + 1) ^ D := by
    have hd : 1 ≤ D := hD
    have hh := Nat.pow_le_pow_right hbase hd
    simpa using hh
  unfold LaurentArithmetic.boxSize
  have he' : 1 ≤ entries := he
  nlinarith

end
end Decoupling.HighDim.AlgorithmInputSize
