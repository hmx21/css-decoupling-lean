import Decoupling.HighDim.AlgorithmTwoInvertibleSolvability

/-! # Fixed representative lift solvability for actual augmented presentations -/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {c0 c1 t0 t1 r : ℕ}
variable {NC NT : Type*} [AddCommGroup NC] [Module R NC] [AddCommGroup NT] [Module R NT]

theorem exists_matrix_lift_of_presentation (d : Matrix (Fin c1) (Fin c0) R)
    (pi : (Fin c1 → R) →ₗ[R] NC) (exact : LinearMap.range d.mulVecLin = LinearMap.ker pi)
    (B : Matrix (Fin c1) (Fin r) R) (hzero : pi.comp B.mulVecLin = 0) :
    ∃ X : Matrix (Fin c0) (Fin r) R, d*X=B := by
  obtain ⟨l,hl⟩ := Comparison.exists_lift_of_comp_eq_zero d.mulVecLin pi B.mulVecLin exact hzero
  refine ⟨LinearMap.toMatrix' l, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact hl

theorem fixed_presentations_lifts
    (dC : Matrix (Fin c1) (Fin c0) R) (dT : Matrix (Fin t1) (Fin t0) R)
    (piC : (Fin c1 → R) →ₗ[R] NC) (piT : (Fin t1 → R) →ₗ[R] NT)
    (exactC : LinearMap.range dC.mulVecLin = LinearMap.ker piC)
    (exactT : LinearMap.range dT.mulVecLin = LinearMap.ker piT)
    (beta : NT ≃ₗ[R] NC) (F : Matrix (Fin c1) (Fin t1) R) (G : Matrix (Fin t1) (Fin c1) R)
    (hF : piC.comp F.mulVecLin = beta.toLinearMap.comp piT)
    (hG : piT.comp G.mulVecLin = beta.symm.toLinearMap.comp piC) :
    (∃ X : Matrix (Fin c0) (Fin t0) R, dC*X=F*dT) ∧
    (∃ X : Matrix (Fin t0) (Fin c0) R, dT*X=G*dC) ∧
    (∃ X : Matrix (Fin c0) (Fin c1) R, dC*X=1-F*G) ∧
    (∃ X : Matrix (Fin t0) (Fin t1) R, dT*X=1-G*F) := by
  have hphi (x : Fin t1 → R) : piC (F*ᵥx)=beta (piT x) := DFunLike.congr_fun hF x
  have hpsi (x : Fin c1 → R) : piT (G*ᵥx)=beta.symm (piC x) := DFunLike.congr_fun hG x
  have hdc (x : Fin c0 → R) : piC (dC*ᵥx)=0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactC]
    exact ⟨x,rfl⟩
  have hdt (x : Fin t0 → R) : piT (dT*ᵥx)=0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactT]
    exact ⟨x,rfl⟩
  refine ⟨exists_matrix_lift_of_presentation dC piC exactC (F*dT) ?_,
    exists_matrix_lift_of_presentation dT piT exactT (G*dC) ?_,
    exists_matrix_lift_of_presentation dC piC exactC (1-F*G) ?_,
    exists_matrix_lift_of_presentation dT piT exactT (1-G*F) ?_⟩
  · apply LinearMap.ext
    intro x
    change piC ((F*dT)*ᵥx)=0
    rw [← Matrix.mulVec_mulVec, hphi, hdt, map_zero]
  · apply LinearMap.ext
    intro x
    change piT ((G*dC)*ᵥx)=0
    rw [← Matrix.mulVec_mulVec, hpsi, hdc, map_zero]
  · apply LinearMap.ext
    intro x
    change piC ((1-F*G)*ᵥx)=0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, map_sub,
      hphi, hpsi, beta.apply_symm_apply, sub_self]
  · apply LinearMap.ext
    intro x
    change piT ((1-G*F)*ᵥx)=0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, map_sub,
      hpsi, hphi, beta.symm_apply_apply, sub_self]

end
end Decoupling.HighDim.AlgorithmTwoInvertible
