import Decoupling.HighDim.HermannInhomogeneousBounds
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Transport a proved solution-degree bound to arbitrary finite row/column labels -/

namespace Decoupling.HighDim.Hermann
open Matrix MvPolynomial
noncomputable section
variable {K : Type*} [CommRing K] {N d : ℕ}

/-- Pull a literal polynomial system solution back across a ring equivalence. -/
theorem ringEquiv_solution_pullback {R S : Type*} [CommRing R] [CommRing S]
    {m n : ℕ} (φ : R ≃+* S) (A : Matrix (Fin m) (Fin n) R)
    (v : Fin m → R) (y : Fin n → S)
    (hy : A.map φ *ᵥ y = φ ∘ v) : A *ᵥ (φ.symm ∘ y) = v := by
  funext i
  apply φ.injective
  change φ.toRingHom ((A *ᵥ (φ.symm ∘ y)) i) = φ.toRingHom (v i)
  rw [φ.toRingHom.map_mulVec]
  have he : φ.toRingHom ∘ (φ.symm ∘ y) = y := by
    funext j
    exact φ.apply_symm_apply (y j)
  rw [he]
  exact congrFun hy i

/-- This only transports the induction hypothesis across finite enumerations.
The displayed hypothesis is exactly the smaller-variable induction statement. -/
theorem bounded_solution_finite_labels
    (IH : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
      (v : Fin m → MvPolynomial (Fin N) K),
      (∀ i j, (A i j).totalDegree ≤ d) → (∀ i, (v i).totalDegree ≤ d) →
      (∃ y, A *ᵥ y = v) → ∃ y, A *ᵥ y = v ∧ ∀ j,
        (y j).totalDegree ≤ solutionBound N m d)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ (MvPolynomial (Fin N) K)) (v : ι → MvPolynomial (Fin N) K)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (hv : ∀ i, (v i).totalDegree ≤ d)
    (hsol : ∃ y, A *ᵥ y = v) :
    ∃ y, A *ᵥ y = v ∧ ∀ j, (y j).totalDegree ≤ solutionBound N (Fintype.card ι) d := by
  let er := Fintype.equivFin ι
  let ec := Fintype.equivFin κ
  let A' := A.submatrix er.symm ec.symm
  let v' := v ∘ er.symm
  have hs : ∃ y, A' *ᵥ y = v' := by
    obtain ⟨y, hy⟩ := hsol
    refine ⟨y ∘ ec.symm, ?_⟩
    rw [Matrix.submatrix_mulVec_equiv]
    simpa [v', Function.comp_def] using congrArg (fun w => w ∘ er.symm) hy
  obtain ⟨y, hy, hdeg⟩ := IH (Fintype.card ι) (Fintype.card κ) A' v'
    (fun i j => hA (er.symm i) (ec.symm j)) (fun i => hv (er.symm i)) hs
  refine ⟨y ∘ ec, ?_, fun j => hdeg (ec j)⟩
  rw [Matrix.submatrix_mulVec_equiv] at hy
  funext i
  simpa [v', Function.comp_def] using congrFun hy (er i)

end
end Decoupling.HighDim.Hermann
