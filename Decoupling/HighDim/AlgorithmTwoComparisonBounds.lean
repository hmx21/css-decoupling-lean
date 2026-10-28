import Decoupling.HighDim.AlgorithmTwoComparisonToric

/-!
# Toric-stack degree bounds independent of its multiplicities

The finite comparison systems use a degree interval controlled by the
spatial dimension, rather than the sum of the copy degrees.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits
noncomputable section
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

theorem stack_strictlyLE (upper : ℤ) (hupper : ∀ i, (forms i : ℤ) + 1 ≤ upper) :
    (Toric.stackModel K D forms).IsStrictlyLE upper := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have hi (i : ι) : IsZero ((Toric.model K D (forms i + 1)).X n) :=
    (Toric.model K D (forms i + 1)).isZero_of_isStrictlyLE (forms i + 1) n
      (lt_of_le_of_lt (hupper i) hn)
  let (i : ι) : Subsingleton ((Toric.model K D (forms i + 1)).X n) :=
    ModuleCat.subsingleton_of_isZero (hi i)
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (Toric.stackTermIso K D forms n)

theorem stack_strictlyGE :
    (Toric.stackModel K D forms).IsStrictlyGE (-(D : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hi (i : ι) : IsZero ((Toric.model K D (forms i + 1)).X n) :=
    (Toric.model K D (forms i + 1)).isZero_of_isStrictlyGE ((forms i : ℤ) + 1 - D) n (by omega)
  let (i : ι) : Subsingleton ((Toric.model K D (forms i + 1)).X n) :=
    ModuleCat.subsingleton_of_isZero (hi i)
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (Toric.stackTermIso K D forms n)

theorem stack_dimension_bounds (hforms : ∀ i, forms i + 1 ≤ D) :
    (Toric.stackModel K D forms).IsStrictlyGE (-(D : ℤ)) ∧
      (Toric.stackModel K D forms).IsStrictlyLE (D : ℤ) :=
  ⟨stack_strictlyGE K D forms, stack_strictlyLE K D forms D (by
    intro i
    exact_mod_cast hforms i)⟩

end
end Decoupling.HighDim.AlgorithmTwoComparison
