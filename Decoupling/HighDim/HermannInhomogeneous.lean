import Decoupling.HighDim.HermannInhomogeneousStep
import Decoupling.HighDim.HermannTransportMonic
import Decoupling.HighDim.EffectiveLinearConstant

/-!
# An unconditional effective solution-degree bound over infinite fields

The induction selects an actual maximal minor, constructs its monic coordinate
change, reduces the actual inhomogeneous equations, solves the coefficient
system in one fewer variable, and transports the solution back. The only
hypotheses on the input system are its entry/right-side degree bounds and
ordinary solvability. No normalization or bounded-solution certificate is input.
-/

namespace Decoupling.HighDim.Hermann
open MvPolynomial Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] [Infinite K]

theorem bounded_solution_infinite (N : ℕ) :
    ∀ (m n d : ℕ) (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
      (v : Fin m → MvPolynomial (Fin N) K),
      (∀ i j, (A i j).totalDegree ≤ d) → (∀ i, (v i).totalDegree ≤ d) →
      (∃ y, A *ᵥ y = v) → ∃ y, A *ᵥ y = v ∧
        ∀ j, (y j).totalDegree ≤ solutionBound N m d := by
  induction N with
  | zero =>
    intro m n d A v hA hv hsol
    exact EffectiveLinear.noVariables_bounded_solution A v hsol
  | succ N ih =>
    intro m n d A v hA hv hsol
    by_cases hd : d = 0
    · subst d
      simpa only [solutionBound_zero_degree] using
        EffectiveLinear.constant_bounded_solution A hA v hv hsol
    obtain ⟨y₀, hy₀⟩ := hsol
    by_cases hAz : A = 0
    · have hvz : v = 0 := by simpa only [hAz, Matrix.zero_mulVec] using hy₀.symm
      refine ⟨0, by rw [Matrix.mulVec_zero, hvz], ?_⟩
      intro j
      simp
    obtain ⟨r, rows, hrm, hker, ⟨M⟩⟩ := exists_monicMinorData A d hA
    have hr : 1 ≤ r := by
      by_contra hn
      have hr0 : r = 0 := by omega
      subst r
      apply hAz
      apply Matrix.mulVec_injective
      funext y
      rw [Matrix.zero_mulVec]
      apply (hker y).mpr
      funext i
      exact Fin.elim0 i
    let B := A.submatrix rows id
    let φ := polynomialCoordinates M.e
    let b := fun i => φ (v (rows i))
    have hs : ∃ y, transformedMatrix M.e B *ᵥ y = b := by
      refine ⟨φ ∘ y₀, ?_⟩
      funext i
      exact (φ.toRingHom.map_mulVec B y₀ i).symm.trans
        (congrArg φ (congrFun hy₀ (rows i)))
    have hb : ∀ i, (flatten (b i)).totalDegree ≤ d := by
      intro i
      change (flatten (polynomialCoordinates M.e (v (rows i)))).totalDegree ≤ d
      simpa only [flatten, polynomialCoordinates, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply, M.preservesDegree] using hv (rows i)
    obtain ⟨z, hz, hdeg⟩ := bounded_solution_normalized
      (fun m n A v => ih m n d A v) hr (by omega) (transformedMatrix M.e B)
      M.H M.E M.δ M.monic M.divisorDegree M.mul_H M.E_eq
      M.matrixDegree M.HDegree M.EDegree b hb hs
    let y := φ.symm ∘ z
    have hBy : B *ᵥ y = v ∘ rows :=
      ringEquiv_solution_pullback φ.toRingEquiv B (v ∘ rows) z hz
    refine ⟨y, (row_solution_equivalence A rows hker v y₀ hy₀ y).mpr hBy, ?_⟩
    intro j
    have he : (y j).totalDegree = (flatten (z j)).totalDegree := by
      change (M.e.symm (flatten (z j))).totalDegree = _
      exact (M.preservesDegree (M.e.symm (flatten (z j)))).symm.trans
        (congrArg MvPolynomial.totalDegree (M.e.apply_symm_apply (flatten (z j))))
    rw [he]
    exact (hdeg j).trans (solutionBound_mono (N + 1) hrm le_rfl)

end
end Decoupling.HighDim.Hermann
