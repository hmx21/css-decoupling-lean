import Decoupling.HighDim.PolynomialLaurentLocalization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Data.Matrix.Mul

/-!
# HD014 exactness of the actual localized polynomial matrices

Flatness follows from the proved localization, and the concrete matrix
statement is also proved directly by clearing one denominator for an
entire vector. All kernels and ranges are the actual matrix maps.
-/
namespace Decoupling.HighDim.PolynomialLaurent
open Matrix
noncomputable section
variable {K : Type*} [CommRing K] {D m n r : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem flat : Module.Flat (Poly D K) (Laurent K D) :=
  IsLocalization.flat (Laurent K D) (positiveMonomials D K)

def mapVector (x : Fin n → Poly D K) : Fin n → Laurent K D := fun i => inclusion D K (x i)

theorem mapVector_injective : Function.Injective (mapVector (K := K) (D := D) (n := n)) := by
  intro x y he
  funext i
  exact inclusion_injective D K (congrFun he i)

@[simp] theorem mapVector_zero : mapVector (0 : Fin n → Poly D K) = 0 := by
  funext i
  exact map_zero _

theorem mapVector_mulVec (A : Matrix (Fin m) (Fin n) (Poly D K)) (x : Fin n → Poly D K) :
    mapVector (A*ᵥx) = A.map (inclusion D K)*ᵥmapVector x := by
  funext i
  exact RingHom.map_mulVec (inclusion D K) A x i

theorem matrix_zero_of_exact (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin n) (Fin r) (Poly D K))
    (hex : ∀ x, A*ᵥx=0 ↔ ∃ y, B*ᵥy=x) : A*B=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  exact (hex (B*ᵥy)).mpr ⟨y,rfl⟩

theorem map_matrix_mul (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin n) (Fin r) (Poly D K)) :
    (A*B).map (inclusion D K) = A.map (inclusion D K)*B.map (inclusion D K) := by
  exact Matrix.map_mul (f := inclusion D K)

theorem localized_exactness (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin n) (Fin r) (Poly D K))
    (hex : ∀ x, A*ᵥx=0 ↔ ∃ y, B*ᵥy=x) (x : Fin n → Laurent K D) :
    A.map (inclusion D K)*ᵥx=0 ↔ ∃ y, B.map (inclusion D K)*ᵥy=x := by
  constructor
  · intro hx
    obtain ⟨h,p,hp⟩ := finite_family_clear x
    have hp' : mapVector p = monomial K (constantExponent D h) • x := by
      funext i
      exact hp i
    have ha : A*ᵥp=0 := by
      apply mapVector_injective
      rw [mapVector_mulVec,hp',Matrix.mulVec_smul,hx,smul_zero,mapVector_zero]
    obtain ⟨y,hy⟩ := (hex p).mp ha
    refine ⟨monomial K (-(constantExponent D h)) • mapVector y,?_⟩
    rw [Matrix.mulVec_smul,←mapVector_mulVec,hy,hp',smul_smul,monomial_neg_mul,one_smul]
  · rintro ⟨y,rfl⟩
    rw [Matrix.mulVec_mulVec,←map_matrix_mul,matrix_zero_of_exact A B hex]
    simp

theorem localized_range_eq_kernel (A : Matrix (Fin m) (Fin n) (Poly D K))
    (B : Matrix (Fin n) (Fin r) (Poly D K))
    (hex : LinearMap.range B.mulVecLin = LinearMap.ker A.mulVecLin) :
    LinearMap.range (B.map (inclusion D K)).mulVecLin =
      LinearMap.ker (A.map (inclusion D K)).mulVecLin := by
  have hx (x : Fin n → Poly D K) : A*ᵥx=0 ↔ ∃ y,B*ᵥy=x := by
    change x ∈ LinearMap.ker A.mulVecLin ↔ x ∈ LinearMap.range B.mulVecLin
    rw [hex]
  ext x
  exact (localized_exactness A B hx x).symm

end
end Decoupling.HighDim.PolynomialLaurent
