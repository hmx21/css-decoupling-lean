import Decoupling.HighDim.Comparison

/-!
# Four lift systems from fixed, actual cokernel representatives

The forward and inverse degree-one matrices are supplied as the explicit
representatives of a genuine quotient isomorphism. All four lift
existence statements follow; none is assumed. Their existential proofs
will only establish success of the actual Laurent solver.
-/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {c0 c1 t0 t1 r : ℕ}

theorem exists_matrix_lift (d : Matrix (Fin c1) (Fin c0) R)
    (B : Matrix (Fin c1) (Fin r) R)
    (hzero : (Comparison.checkQuotient d).comp B.mulVecLin = 0) :
    ∃ X : Matrix (Fin c0) (Fin r) R, d*X=B := by
  obtain ⟨l,hl⟩ := Comparison.exists_lift_of_comp_eq_zero d.mulVecLin
    (Comparison.checkQuotient d) B.mulVecLin (Submodule.ker_mkQ _).symm hzero
  refine ⟨LinearMap.toMatrix' l, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact hl

theorem fixed_representatives_lifts
    (dC : Matrix (Fin c1) (Fin c0) R) (dT : Matrix (Fin t1) (Fin t0) R)
    (beta : Comparison.CheckCokernel dT ≃ₗ[R] Comparison.CheckCokernel dC)
    (F : Matrix (Fin c1) (Fin t1) R) (G : Matrix (Fin t1) (Fin c1) R)
    (hF : (Comparison.checkQuotient dC).comp F.mulVecLin =
      beta.toLinearMap.comp (Comparison.checkQuotient dT))
    (hG : (Comparison.checkQuotient dT).comp G.mulVecLin =
      beta.symm.toLinearMap.comp (Comparison.checkQuotient dC)) :
    (∃ X : Matrix (Fin c0) (Fin t0) R, dC*X=F*dT) ∧
    (∃ X : Matrix (Fin t0) (Fin c0) R, dT*X=G*dC) ∧
    (∃ X : Matrix (Fin c0) (Fin c1) R, dC*X=1-F*G) ∧
    (∃ X : Matrix (Fin t0) (Fin t1) R, dT*X=1-G*F) := by
  have hphi (x : Fin t1 → R) : Comparison.checkQuotient dC (F *ᵥ x) =
      beta (Comparison.checkQuotient dT x) := DFunLike.congr_fun hF x
  have hpsi (x : Fin c1 → R) : Comparison.checkQuotient dT (G *ᵥ x) =
      beta.symm (Comparison.checkQuotient dC x) := DFunLike.congr_fun hG x
  have hdc (x : Fin c0 → R) : Comparison.checkQuotient dC (dC*ᵥx)=0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨x,rfl⟩
  have hdt (x : Fin t0 → R) : Comparison.checkQuotient dT (dT*ᵥx)=0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨x,rfl⟩
  refine ⟨exists_matrix_lift dC (F*dT) ?_, exists_matrix_lift dT (G*dC) ?_,
    exists_matrix_lift dC (1-F*G) ?_, exists_matrix_lift dT (1-G*F) ?_⟩
  · apply LinearMap.ext
    intro x
    change Comparison.checkQuotient dC ((F*dT)*ᵥx)=0
    rw [← Matrix.mulVec_mulVec, hphi, hdt, map_zero]
  · apply LinearMap.ext
    intro x
    change Comparison.checkQuotient dT ((G*dC)*ᵥx)=0
    rw [← Matrix.mulVec_mulVec, hpsi, hdc, map_zero]
  · apply LinearMap.ext
    intro x
    change Comparison.checkQuotient dC ((1-F*G)*ᵥx)=0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, map_sub,
      hphi, hpsi, beta.apply_symm_apply, sub_self]
  · apply LinearMap.ext
    intro x
    change Comparison.checkQuotient dT ((1-G*F)*ᵥx)=0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, map_sub,
      hpsi, hphi, beta.symm_apply_apply, sub_self]

end
end Decoupling.HighDim.AlgorithmTwoInvertible
