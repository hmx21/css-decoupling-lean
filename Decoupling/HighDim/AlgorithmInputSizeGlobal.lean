import Decoupling.HighDim.AlgorithmInputSize
import Decoupling.HighDim.AlgorithmTwoComputedLayersWindow
import Mathlib.Data.Int.Interval

/-!
# HD012 finite-complex rank budget from the paper's dense coefficient count

The homology action is transferred through the genuine coordinate window.
Consequently isolated free terms are excluded by the actual profile
condition. The final numerical bound counts only the coefficients of
the original adjacent differentials, rather than a padded square matrix.
-/
namespace Decoupling.HighDim.AlgorithmInputSize
open Matrix CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def rankSum (r : ℤ → ℕ) (L : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc (-(L : ℤ)) L, r j

def entryCount (r : ℤ → ℕ) (L : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc (-(L : ℤ)) L, r j * r (j+1)

def denseSize (r : ℤ → ℕ) (D L h : ℕ) : ℕ :=
  entryCount r L * LaurentArithmetic.boxSize D h

theorem interval_card (L : ℕ) : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2*L+1 := by
  rw [Int.card_Icc]
  omega

theorem rankSum_le_entries (r : ℤ → ℕ) (L : ℕ)
    (hleft : r (-(L : ℤ)-1) = 0)
    (hadj : ∀ j ∈ Finset.Icc (-(L : ℤ)) L, r j ≤ r (j-1)*r j + r j*r (j+1)) :
    rankSum r L ≤ 2*(2*L+1)*entryCount r L := by
  have hr (j : ℤ) (hj : j ∈ Finset.Icc (-(L : ℤ)) L) :
      r j*r (j+1) ≤ entryCount r L := by
    exact Finset.single_le_sum (f := fun i => r i*r (i+1)) (fun _ _ => Nat.zero_le _) hj
  have hl (j : ℤ) (hj : j ∈ Finset.Icc (-(L : ℤ)) L) :
      r (j-1)*r j ≤ entryCount r L := by
    by_cases he : j = -(L : ℤ)
    · subst j
      rw [hleft, zero_mul]
      exact Nat.zero_le _
    · have hm : j-1 ∈ Finset.Icc (-(L : ℤ)) L := by
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      simpa using hr (j-1) hm
  calc
    rankSum r L ≤ ∑ _j ∈ Finset.Icc (-(L : ℤ)) L, 2*entryCount r L := by
      apply Finset.sum_le_sum
      intro j hj
      have := hadj j hj
      have := hr j hj
      have := hl j hj
      omega
    _ = _ := by
      rw [Finset.sum_const, interval_card]
      simp only [nsmul_eq_mul, Nat.cast_id]
      ring

theorem entries_le_dense (r : ℤ → ℕ) (D L h : ℕ) : entryCount r L ≤ denseSize r D L h := by
  have hb : 1 ≤ LaurentArithmetic.boxSize D h := Nat.one_le_pow _ _ (by omega)
  unfold denseSize
  nlinarith

theorem dense_budget (r : ℤ → ℕ) (D L h : ℕ) (hD : 0 < D)
    (hleft : r (-(L : ℤ)-1) = 0)
    (hadj : ∀ j ∈ Finset.Icc (-(L : ℤ)) L, r j ≤ r (j-1)*r j + r j*r (j+1))
    (hnonzero : 0 < rankSum r L) :
    rankSum r L + h ≤ (2*(2*L+1)+1)*denseSize r D L h := by
  have hr := rankSum_le_entries r L hleft hadj
  have he : 0 < entryCount r L := by nlinarith
  have hb := radius_le_dense_size D h (entryCount r L) hD he
  have he' := entries_le_dense r D L h
  have htotal := Nat.mul_le_mul_left (2*(2*L+1)) he'
  change h ≤ denseSize r D L h at hb
  nlinarith

variable {K : Type} [Field K] {D : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)

def coordinateDifferential (i j : ℤ) :
    Matrix (Fin (coords.rank j)) (Fin (coords.rank i)) (Laurent K D) :=
  LinearMap.toMatrix' ((coords.equiv j).toLinearMap.comp
    ((C.d i j).hom.comp (coords.equiv i).symm.toLinearMap))

theorem coordinateDifferential_action (i j : ℤ) (v : C.X i) :
    coordinateDifferential coords i j *ᵥ coords.equiv i v = coords.equiv j (C.d i j v) := by
  rw [coordinateDifferential, LinearMap.toMatrix'_mulVec]
  change coords.equiv j (C.d i j ((coords.equiv i).symm (coords.equiv i v))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem native_adjacent_rank (hD : 0 < D) (j : ℤ)
    (hH : TrivialLayers.AugmentationAction (C.homology j)) :
    coords.rank j ≤ coords.rank (j-1)*coords.rank j + coords.rank j*coords.rank (j+1) := by
  let b := coordinateDifferential coords (j-1) j
  let d := coordinateDifferential coords j (j+1)
  have hb := coordinateDifferential_action coords (j-1) j
  have hd := coordinateDifferential_action coords j (j+1)
  have hbd : d*b=0 := AlgorithmTwoComputedLayers.window_product_zero coords j b d hb hd
  have hw := TrivialLayers.augmentationAction_of_iso
    (AlgorithmTwoComputedLayers.windowNativeIso coords j b d hb hd hbd) hH
  exact adjacent_rank_bound hD b d hbd hw

theorem rank_zero_of_isZero (j : ℤ) (hz : IsZero (C.X j)) : coords.rank j = 0 := by
  let : Subsingleton (C.X j) := ModuleCat.subsingleton_of_isZero hz
  let : Subsingleton (StableFree.Power (Laurent K D) (coords.rank j)) :=
    (coords.equiv j).symm.injective.subsingleton
  by_contra hn
  let k : Fin (coords.rank j) := ⟨0, Nat.pos_of_ne_zero hn⟩
  have he := congrFun
    (Subsingleton.elim (0 : StableFree.Power (Laurent K D) (coords.rank j)) 1) k
  exact zero_ne_one he

/-- For the actual bounded input model, the paper's dense coefficient
count controls both its total free rank and its common exponent radius. -/
theorem native_dense_budget (L h : ℕ) (hD : 0 < D)
    [C.IsStrictlyGE (-(L : ℤ))]
    (hH : ∀ j : ℤ, TrivialLayers.AugmentationAction (C.homology j))
    (hnonzero : 0 < rankSum coords.rank L) :
    rankSum coords.rank L + h ≤
      (2*(2*L+1)+1)*denseSize coords.rank D L h := by
  apply dense_budget coords.rank D L h hD _ _ hnonzero
  · exact rank_zero_of_isZero coords _ (C.isZero_of_isStrictlyGE (-(L : ℤ)) _ (by omega))
  · intro j _
    exact native_adjacent_rank coords hD j (hH j)

end
end Decoupling.HighDim.AlgorithmInputSize
