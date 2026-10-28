import Decoupling.HighDim.DecouplingCriterion

/-!
# HD010 Lemmas 12–14 with one common lift and one common circuit

An actual stable check-cokernel equivalence is constructed from the native
profile. After identity checks absorb its free summands, comparison maps
lifting that very equivalence are constructed. The same comparison data
supply U,V, their inverses, the commuting square, and the compiled gate word.
-/
namespace Decoupling.HighDim.PaperConstruction
open CategoryTheory PhysicalIsomorphism Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}
variable {C₀ C₁ C₂ T₀ T₁ T₂ : Type}
  [Fintype C₀] [Fintype C₁] [Fintype C₂] [Fintype T₀] [Fintype T₁] [Fintype T₂]
  [DecidableEq C₀] [DecidableEq C₁] [DecidableEq T₀] [DecidableEq T₁]

/-- Actual lifts of the specified quotient isomorphism and its inverse. -/
structure Lift (dC : Matrix C₁ C₀ (Laurent K D)) (dT : Matrix T₁ T₀ (Laurent K D))
    (beta : Comparison.CheckCokernel dT ≃ₗ[(Laurent K D)] Comparison.CheckCokernel dC) where
  data : Stabilization.ComparisonData (Laurent K D) C₀ C₁ T₀ T₁
  code_eq : data.dC = dC
  target_eq : data.dT = dT
  lift_beta : (Comparison.checkQuotient dC).comp data.phi1.mulVecLin =
    beta.toLinearMap.comp (Comparison.checkQuotient dT)
  lift_inverse : (Comparison.checkQuotient dT).comp data.psi1.mulVecLin =
    beta.symm.toLinearMap.comp (Comparison.checkQuotient dC)

/-- Lemma 13: all comparison identities are proved, rather than premises. -/
def lift (dC : Matrix C₁ C₀ (Laurent K D)) (dT : Matrix T₁ T₀ (Laurent K D))
    (beta : Comparison.CheckCokernel dT ≃ₗ[(Laurent K D)] Comparison.CheckCokernel dC) : Lift dC dT beta :=
  let h := Comparison.exists_comparisonData dC dT beta
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2.1,
    (Classical.choose_spec h).2.2.1, (Classical.choose_spec h).2.2.2⟩

variable {dC : Matrix C₁ C₀ (Laurent K D)} {dT : Matrix T₁ T₀ (Laurent K D)}
  {beta : Comparison.CheckCokernel dT ≃ₗ[(Laurent K D)] Comparison.CheckCokernel dC}
  (L : Lift dC dT beta)

/-- Both inverses and the actual stabilized check square use this same lift. -/
theorem invertible_lift :
    (L.data.U * L.data.UInv = 1 ∧ L.data.UInv * L.data.U = 1) ∧
    (L.data.V * L.data.VInv = 1 ∧ L.data.VInv * L.data.V = 1) ∧
    StableCSS.H_X (A := C₁) (B := C₀ ⊕ T₁) dT * L.data.U =
      L.data.V * StableCSS.H_X (A := T₁) (B := T₀ ⊕ C₁) dC := by
  refine ⟨L.data.U_inverse, L.data.V_inverse, ?_⟩
  simpa [Stabilization.ComparisonData.dCHat, Stabilization.ComparisonData.dCPrime,
    Stabilization.ComparisonData.dTHat, Stabilization.ComparisonData.dTPrime,
    StableCSS.H_X, L.code_eq, L.target_eq] using L.data.stabilized_square

/-- The physical word realizes the U and UInv of the specified lift, with
both actual stabilized images and every locality property retained. -/
structure Realization (zC : Matrix C₀ C₂ (Laurent K D)) (zT : Matrix T₀ T₂ (Laurent K D)) where
  gates : List (Circuit.Layer K D ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁)))
  z_action : Circuit.wordZ gates = L.data.U.submatrix id (Equiv.sumComm _ _).symm
  x_action : Circuit.wordX gates = dagger (L.data.UInv.submatrix (Equiv.sumComm _ _).symm id)
  transports : Transports gates (Equiv.sumComm _ _)
    (StableCSS.H_X (A := T₁) (B := T₀ ⊕ C₁) dC)
    (StableCSS.H_X (A := C₁) (B := C₀ ⊕ T₁) dT)
    (StableCSS.H_Z_dagger (A := T₁) (B := T₀ ⊕ C₁) zC)
    (StableCSS.H_Z_dagger (A := C₁) (B := C₀ ⊕ T₁) zT)
  locality : LocalCircuit gates

/-- Lemma 14: the same U from Lemma 13 is compiled into the physical word. -/
theorem realization_exists (zC : Matrix C₀ C₂ (Laurent K D)) (zT : Matrix T₀ T₂ (Laurent K D))
    (hC : ∀ v, dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, dT *ᵥ v = 0 ↔ inImage zT v) : Nonempty (Realization L zC zT) := by
  obtain ⟨gates, hz, hx, _⟩ := Circuit.theta_circuit L.data.psiHat L.data.phiHat (Equiv.sumComm _ _)
  refine ⟨⟨gates, hz, hx, ?_, localCircuit gates⟩⟩
  apply transports_of_actions gates (Equiv.sumComm _ _) _ _ _ _
    L.data.U L.data.UInv L.data.V L.data.VInv
    L.data.U_inverse.1 L.data.V_inverse.2 (invertible_lift L).2.2
  · exact StableCSS.exactness dC zC hC
  · exact StableCSS.exactness dT zT hT
  · exact hz
  · exact hx

section Profile
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)
  {q s r : ℕ} (c : CSS.Checks K D q s r)

/-- Lemma 12 is stated for the actual check cokernels and arbitrary native
split-profile multiplicities; no comparison or circuit data are inputs. -/
theorem stable_cokernel (hc : c.Topological) (h : Profile.S_X c ≅ Toric.splitTarget K D forms) :
    ∃ a b : ℕ, Nonempty
      (((Toric.stackChecks K D forms).CheckCokernel × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (c.CheckCokernel × (Fin a → Laurent K D))) :=
  Toric.stableCheckCokernel_of_split K D forms c hc h

/-- The full Lemma 12 → 13 → 14 construction, preserving one quotient
isomorphism, its actual lifts, the same U/V, and the same physical word. -/
theorem construction_from_profile (hc : c.Topological)
    (h : Profile.S_X c ≅ Toric.splitTarget K D forms) :
    ∃ (a b : ℕ) (beta :
      ((Toric.stackChecks K D forms).CheckCokernel × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (c.CheckCokernel × (Fin a → Laurent K D))),
      let beta' := (StableCSS.identityCheckCokernelEquiv (A := Fin b)
        (Toric.stackChecks K D forms).H_X).trans
          (beta.trans (StableCSS.identityCheckCokernelEquiv (A := Fin a) c.H_X).symm)
      Nonempty (Realization
        (lift (StableCSS.identityChecks (A := Fin a) c.H_X)
          (StableCSS.identityChecks (A := Fin b) (Toric.stackChecks K D forms).H_X) beta')
        (dagger c.H_Z) (dagger (Toric.stackChecks K D forms).H_Z)) := by
  classical
  obtain ⟨a, b, ⟨beta⟩⟩ := stable_cokernel K D forms c hc h
  refine ⟨a, b, beta, ?_⟩
  apply realization_exists
  · intro v
    exact (StableCSS.identityChecks_kernel c.H_X v).trans (c.exact_X hc v)
  · intro v
    exact (StableCSS.identityChecks_kernel (Toric.stackChecks K D forms).H_X v).trans
      (Toric.stackChecks_exact_X K D forms v)

end Profile
end
end Decoupling.HighDim.PaperConstruction
