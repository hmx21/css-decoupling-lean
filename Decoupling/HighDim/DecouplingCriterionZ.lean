import Decoupling.HighDim.DecouplingCriterion

/-!
# HD010 Theorem 1 in the Z sector

The physical condition is the actual Fourier-dual SUM/SWAP transport,
with arbitrary existential toric multiplicities. The same subgroup is used
throughout; complementary dual-cell geometry is supplied explicitly.
-/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory ScalingLattice PhysicalIsomorphism
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ} {ι : Type} [Fintype ι]
  (forms : ι → ℕ) {q s r : ℕ}

/-- Fourier conjugation is reversible on both actual stabilized sectors. -/
theorem dual_iff_swap (c : CSS.Checks K D q s r) :
    Toric.DecouplesToDualStack K D forms c ↔ Toric.DecouplesToStack K D forms c.swap := by
  constructor
  · rintro ⟨a, b, gates, ht, _⟩
    refine ⟨a, b, gates.map Circuit.fourierDual, ?_, localCircuit _⟩
    simpa only [CSS.Checks.swap, dagger_dagger] using transports_fourierDual gates _ _ _ _ _ ht
  · exact Toric.decouples_dual_of_swap K D forms c

variable {p : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

def DecouplesOnZ : Prop :=
  ∃ t : Fin (D - 1) → ℕ, Toric.DecouplesToDualStack (ZMod p) D (Toric.copyForms D t)
    (physicalChecks (ZMod p) Λ e c)

theorem theorem1_Z (hc : c.Topological) :
    DecouplesOnZ Λ e c ↔ HasToricProfile Λ e c.swap := by
  change (∃ t, Toric.DecouplesToDualStack (ZMod p) D (Toric.copyForms D t)
    (physicalChecks (ZMod p) Λ e c)) ↔ _
  simp only [dual_iff_swap]
  exact theorem1_X Λ e c.swap (c.topological_swap hc)

def complementaryForms (t : Fin (D - 1) → ℕ) : Toric.Copies D t → ℕ :=
  fun i => D - i.1.val - 2

theorem complementary_degree (t : Fin (D - 1) → ℕ) (i : Toric.Copies D t) :
    Toric.copyForms D t i + complementaryForms t i + 2 = D := by
  have := i.1.isLt
  dsimp [Toric.copyForms, complementaryForms]
  omega

/-- The Z-side criterion produces the actual complementary toric stack
TC_(D-j), with the proved dual-cell map and the same retained-lattice word. -/
theorem complementary_of_profile (hc : c.Topological) (h : HasToricProfile Λ e c.swap) :
    ∃ t : Fin (D - 1) → ℕ, Toric.DecouplesToComplementaryStack (ZMod p) D
      (Toric.copyForms D t) (complementaryForms t) (complementary_degree t)
      (physicalChecks (ZMod p) Λ e c) := by
  obtain ⟨t, ht⟩ := (theorem1_Z Λ e c hc).mpr h
  exact ⟨t, Toric.decouples_complementary_of_dual (ZMod p) D (Toric.copyForms D t)
    (complementaryForms t) (complementary_degree t) _ ht⟩

end
end Decoupling.HighDim.DecouplingCriterion
