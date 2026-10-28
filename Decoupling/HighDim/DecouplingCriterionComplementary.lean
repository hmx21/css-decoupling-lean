import Decoupling.HighDim.DecouplingCriterionZ

/-! # Reversible complementary dual-cell identification in Theorem 1 -/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory PhysicalIsomorphism Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

private theorem exists_map_iff {A B C : Type*} (u : B → C) (hu : Function.Injective u)
    (f : A → B) (v : B) : (∃ z, u (f z) = u v) ↔ ∃ z, f z = v :=
  ⟨fun ⟨z, h⟩ => ⟨z, hu h⟩, fun ⟨z, h⟩ => ⟨z, congrArg u h⟩⟩

theorem transports_of_after_images
    {Q Q' Q'' C C' C'' Z Z' Z'' : Type}
    [Fintype Q] [Fintype Q'] [Fintype Q'']
    [Fintype C] [Fintype C'] [Fintype C'']
    [Fintype Z] [Fintype Z'] [Fintype Z''] [DecidableEq Q']
    (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (U : Matrix Q'' Q' (Laurent K D))
    (HC : Matrix C Q (Laurent K D)) (HM : Matrix C' Q' (Laurent K D))
    (HT : Matrix C'' Q'' (Laurent K D)) (BC : Matrix Q Z (Laurent K D))
    (BM : Matrix Q' Z' (Laurent K D)) (BT : Matrix Q'' Z'' (Laurent K D))
    (hu : Function.Injective (fun v => U *ᵥ v))
    (ht : TransportsAfter gates e U HC HT BC BT)
    (hz : ∀ v, (∃ z, U *ᵥ (BM *ᵥ z) = v) ↔ inImage BT v)
    (hx : ∀ v, (∃ z, U *ᵥ (dagger HM *ᵥ z) = v) ↔ inImage (dagger HT) v) :
    Transports gates e HC HM BC BM := by
  constructor
  · intro v
    exact (exists_map_iff _ hu _ v).symm.trans
      ((ht.1 (U *ᵥ v)).trans ((hz (U *ᵥ v)).symm.trans (exists_map_iff _ hu _ v)))
  · intro v
    exact (exists_map_iff _ hu _ v).symm.trans
      ((ht.2 (U *ᵥ v)).trans ((hx (U *ᵥ v)).symm.trans (exists_map_iff _ hu _ v)))

variable (K) (D) {ι : Type} [Fintype ι]
  (forms complements : ι → ℕ) (hd : ∀ i, forms i + complements i + 2 = D)
  {q s r : ℕ} (c : CSS.Checks K D q s r)

/-- Complementary dual-cell geometry is an invertible physical relabeling,
so the explicit composite target condition is equivalent in both directions. -/
theorem complementary_iff_dual :
    Toric.DecouplesToComplementaryStack K D forms complements hd c ↔
      Toric.DecouplesToDualStack K D forms c := by
  constructor
  · rintro ⟨a, b, gates, ht, hlocal⟩
    refine ⟨a, b, gates, ?_, hlocal⟩
    refine transports_of_after_images gates (Equiv.sumComm _ _)
      (ancillaryExtension (A := Fin r ⊕ Fin a)
        (B := Fin q ⊕ (Fin (Toric.stackCount D forms 0) ⊕ Fin b))
        (Toric.stackDualMatrix K D forms complements hd)) _ _ _ _ _ _ ?_ ht ?_ ?_
    · intro v w h
      have hi := ancillaryExtension_dagger_mul
        (A := Fin r ⊕ Fin a) (B := Fin q ⊕ (Fin (Toric.stackCount D forms 0) ⊕ Fin b))
        (Toric.stackDualMatrix K D forms complements hd)
        (Toric.stackDualMatrix_dagger_mul K D forms complements hd)
      have hh := congrArg (fun x => dagger (ancillaryExtension
        (A := Fin r ⊕ Fin a) (B := Fin q ⊕ (Fin (Toric.stackCount D forms 0) ⊕ Fin b))
          (Toric.stackDualMatrix K D forms complements hd)) *ᵥ x) h
      simpa only [mulVec_mulVec, hi, one_mulVec] using hh
    · exact ancillaryExtension_X_image _ _ _
        (Toric.stackDual_z_stabilizers K D forms complements hd)
    · simpa only [dagger_dagger] using
        ancillaryExtension_Z_image (A := Fin r ⊕ Fin a)
          (B := Fin q ⊕ (Fin (Toric.stackCount D forms 0) ⊕ Fin b))
          (Toric.stackDualMatrix K D forms complements hd)
          (dagger (Toric.stackChecks K D forms).H_Z)
          (dagger (Toric.stackChecks K D complements).H_X)
          (Toric.stackDual_x_stabilizers K D forms complements hd)
  · exact Toric.decouples_complementary_of_dual K D forms complements hd c

variable {p : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c₀ : CSS.Checks (ZMod p) D q s r)

/-- The Z criterion with the actual complementary toric target, in both
directions, without finite native layers as a premise. -/
theorem theorem1_Z_complementary (hc : c₀.Topological) :
    (∃ t : Fin (D - 1) → ℕ, Toric.DecouplesToComplementaryStack (ZMod p) D
      (Toric.copyForms D t) (complementaryForms t) (complementary_degree t)
      (ScalingLattice.physicalChecks (ZMod p) Λ e c₀)) ↔ HasToricProfile Λ e c₀.swap := by
  simp only [complementary_iff_dual]
  exact theorem1_Z Λ e c₀ hc

end
end Decoupling.HighDim.DecouplingCriterion
