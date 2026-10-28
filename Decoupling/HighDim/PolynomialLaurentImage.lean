import Decoupling.HighDim.PolynomialLaurentMatrix

/-! # HD014 images of the actual polynomial generator matrices localize faithfully -/
namespace Decoupling.HighDim.PolynomialLaurent
open Matrix
noncomputable section
variable {K : Type*} [CommRing K] {D m n r : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem localized_range_mono (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin m) (Fin r) (Poly D K))
    (hAB : LinearMap.range A.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    LinearMap.range (A.map (inclusion D K)).mulVecLin ≤
      LinearMap.range (B.map (inclusion D K)).mulVecLin := by
  rintro x ⟨y,rfl⟩
  obtain ⟨h,p,hp⟩ := finite_family_clear y
  have hp' : mapVector p = monomial K (constantExponent D h) • y := by
    funext i
    exact hp i
  have hz : A*ᵥp ∈ LinearMap.range B.mulVecLin := hAB ⟨p,rfl⟩
  obtain ⟨z,hz⟩ := hz
  change B*ᵥz=A*ᵥp at hz
  refine ⟨monomial K (-(constantExponent D h)) • mapVector z,?_⟩
  change B.map (inclusion D K)*ᵥ(monomial K (-(constantExponent D h)) • mapVector z) =
    A.map (inclusion D K)*ᵥy
  rw [Matrix.mulVec_smul,←mapVector_mulVec,hz,mapVector_mulVec,hp',
    Matrix.mulVec_smul,smul_smul,monomial_neg_mul,one_smul]

theorem localized_range_eq (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin m) (Fin r) (Poly D K))
    (hAB : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    LinearMap.range (A.map (inclusion D K)).mulVecLin =
      LinearMap.range (B.map (inclusion D K)).mulVecLin :=
  le_antisymm (localized_range_mono A B hAB.le) (localized_range_mono B A hAB.ge)

/-- The first matrix of a resolution of the cleared polynomial submodule
still presents the original Laurent image, not a different source module. -/
theorem augmentation_range_original
    (A : Matrix (Fin m) (Fin n) (Laurent K D)) (B : ClearedMatrix A)
    (e : Matrix (Fin m) (Fin r) (Poly D K))
    (he : LinearMap.range e.mulVecLin = LinearMap.range B.matrix.mulVecLin) :
    LinearMap.range (e.map (inclusion D K)).mulVecLin = LinearMap.range A.mulVecLin :=
  (localized_range_eq e B.matrix he).trans B.range_eq

end
end Decoupling.HighDim.PolynomialLaurent
