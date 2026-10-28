import Decoupling.MonicResidue
import Mathlib.RingTheory.Localization.Integer

/-!
# Polynomial-part surjectivity in the local Horrocks argument

This module connects residue normalization to the proved finite-quotient
Nakayama step. All maps act on actual finite polynomial vectors.
-/

namespace Decoupling.HorrocksProjection

open MonicLocalization MonicResidue Polynomial Matrix

noncomputable section

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Fractions whose residues are polynomials form a genuine subring. -/
def residuePolynomialSubring : Subring (MonicFrac A) :=
  (algebraMap (IsLocalRing.ResidueField A)[X]
    (MonicFrac (IsLocalRing.ResidueField A))).range.comap (residueMap A)

theorem polynomialInclusion_mem (p : A[X]) :
    polynomialInclusion p ∈ residuePolynomialSubring (A := A) :=
  ⟨p.map (IsLocalRing.residue A), (mapCoefficients_polynomialInclusion _ _).symm⟩

/-- For a residue-polynomial fraction, taking polynomial part leaves its
residue unchanged. -/
theorem residue_polynomialPart {a : MonicFrac A}
    (ha : a ∈ residuePolynomialSubring (A := A)) :
    residueMap A (polynomialInclusion (polynomialPart a)) = residueMap A a := by
  obtain ⟨p, hp⟩ := ha
  have h := congrArg polynomialPart hp
  rw [polynomialPart_algebraMap, polynomialPart_mapCoefficients] at h
  rw [mapCoefficients_polynomialInclusion, ← h]
  exact hp

theorem polynomial_mem_maximal_smul_of_residue_zero (p : A[X])
    (hp : p.map (IsLocalRing.residue A) = 0) :
    p ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A A[X]) := by
  rw [Ideal.smul_top_eq_map]
  change p ∈ (IsLocalRing.maximalIdeal A).map C
  rw [← IsLocalRing.ker_residue, ← Polynomial.ker_mapRingHom]
  exact hp

/-- Coefficientwise zero residue is exactly the implication needed for
generation modulo the maximal ideal. -/
theorem vector_mem_maximal_smul_of_residue_zero {ι : Type*} [Fintype ι]
    (v : ι → A[X]) (hv : ∀ i, (v i).map (IsLocalRing.residue A) = 0) :
    v ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (ι → A[X])) := by
  classical
  rw [← LinearMap.sum_single_apply (fun _ : ι => A[X]) v]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A)
    (LinearMap.single A (fun _ : ι => A[X]) i)
    (polynomial_mem_maximal_smul_of_residue_zero (v i) (hv i))

variable {m n : Type*} [Fintype m] [Fintype n]

def vectorInclusion : (n → A[X]) →ₗ[A] (n → MonicFrac A) :=
  LinearMap.pi fun i => polynomialInclusion.comp (LinearMap.proj i)

def vectorPart : (m → MonicFrac A) →ₗ[A] (m → A[X]) :=
  LinearMap.pi fun i => polynomialPart.comp (LinearMap.proj i)

/-- The map `v ↦ [Bv]` over the coefficient ring. -/
def projectedMulVec (B : Matrix m n (MonicFrac A)) : (n → A[X]) →ₗ[A] (m → A[X]) :=
  vectorPart.comp ((B.mulVecLin.restrictScalars A).comp vectorInclusion)

omit [Fintype m] in
@[simp] theorem projectedMulVec_apply (B : Matrix m n (MonicFrac A)) (v : n → A[X]) (i : m) :
    projectedMulVec B v i = polynomialPart ((B *ᵥ fun j => polynomialInclusion (v j)) i) := rfl

/-- A normalized right inverse supplies generation modulo the maximal ideal. -/
theorem projectedMulVec_mod_maximal [DecidableEq m] (B : Matrix m n (MonicFrac A))
    (D : Matrix n m (MonicFrac A)) (hBD : B * D = 1)
    (hD : ∀ i j, D i j ∈ residuePolynomialSubring (A := A)) :
    LinearMap.range (projectedMulVec B) ⊔
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (m → A[X])) = ⊤ := by
  classical
  apply top_unique
  intro v _
  let x : n → MonicFrac A := D *ᵥ fun j => polynomialInclusion (v j)
  let w : n → A[X] := fun i => polynomialPart (x i)
  have hx (i : n) : x i ∈ residuePolynomialSubring (A := A) := by
    apply (residuePolynomialSubring (A := A)).sum_mem
    intro j _
    exact (residuePolynomialSubring (A := A)).mul_mem (hD i j)
      (polynomialInclusion_mem (v j))
  have hw : (fun j => residueMap A (polynomialInclusion (w j))) = fun j => residueMap A (x j) := by
    funext j
    exact residue_polynomialPart (hx j)
  have hres (i : m) : residueMap A ((B *ᵥ fun j => polynomialInclusion (w j)) i) =
      residueMap A (polynomialInclusion (v i)) := by
    rw [RingHom.map_mulVec]
    change (B.map (residueMap A) *ᵥ (fun j => residueMap A (polynomialInclusion (w j)))) i = _
    rw [hw]
    refine (RingHom.map_mulVec (residueMap A) B x i).symm.trans ?_
    change residueMap A ((B *ᵥ (D *ᵥ fun j => polynomialInclusion (v j))) i) = _
    rw [Matrix.mulVec_mulVec, hBD, Matrix.one_mulVec]
  have hdiff : v - projectedMulVec B w ∈
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A (m → A[X])) := by
    apply vector_mem_maximal_smul_of_residue_zero
    intro i
    have heq := congrArg polynomialPart (hres i)
    rw [polynomialPart_mapCoefficients, mapCoefficients_polynomialInclusion,
      polynomialPart_polynomialInclusion] at heq
    change (v i - polynomialPart ((B *ᵥ fun j => polynomialInclusion (w j)) i)).map
      (IsLocalRing.residue A) = 0
    rw [Polynomial.map_sub, heq, sub_self]
  have hsum := Submodule.add_mem_sup (show projectedMulVec B w ∈
    LinearMap.range (projectedMulVec B) from ⟨w, rfl⟩) hdiff
  simpa only [add_sub_cancel] using hsum

/-- A common monic denominator of a right inverse gives all monic
multiples inside the polynomial-part image. -/
theorem projectedMulVec_contains_monic_multiples [DecidableEq m]
    (B : Matrix m n (MonicFrac A)) (D : Matrix n m (MonicFrac A)) (hBD : B * D = 1) :
    ∃ h : monicSubmonoid A, ∀ v : m → A[X],
      (fun i => (h : A[X]) * v i) ∈ LinearMap.range (projectedMulVec B) := by
  classical
  let f := algebraMap A[X] (MonicFrac A)
  obtain ⟨h, hh⟩ := IsLocalization.exist_integer_multiples_of_finite (monicSubmonoid A)
    (fun ij : n × m => D ij.1 ij.2)
  change ∀ ij : n × m, ∃ p : A[X], f p = (h : A[X]) • D ij.1 ij.2 at hh
  choose P hP using hh
  let Dp : Matrix n m A[X] := fun i j => P (i, j)
  have hDp : Dp.map f = f h • D := by
    funext i j
    change f (P (i, j)) = f h * D i j
    simpa only [Algebra.smul_def] using hP (i, j)
  refine ⟨h, ?_⟩
  intro v
  refine ⟨Dp *ᵥ v, ?_⟩
  funext i
  rw [projectedMulVec_apply]
  have hvec : (fun j => polynomialInclusion ((Dp *ᵥ v) j)) =
      Dp.map f *ᵥ (fun j => polynomialInclusion (v j)) := by
    funext j
    exact f.map_mulVec Dp v j
  rw [hvec, hDp, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    hBD, Matrix.one_mulVec]
  change polynomialPart (f h * f (v i)) = (h : A[X]) * v i
  rw [← map_mul, polynomialPart_algebraMap]

/-- The full polynomial-part surjectivity step: a normalized right inverse
implies that every finite polynomial vector is a polynomial part of `Bv`.
Both finite generation and Nakayama's hypothesis are proved upstream. -/
theorem projectedMulVec_surjective [DecidableEq m]
    (B : Matrix m n (MonicFrac A)) (D : Matrix n m (MonicFrac A)) (hBD : B * D = 1)
    (hD : ∀ i j, D i j ∈ residuePolynomialSubring (A := A)) :
    Function.Surjective (projectedMulVec B) := by
  obtain ⟨h, hW⟩ := projectedMulVec_contains_monic_multiples B D hBD
  apply LinearMap.range_eq_top.mp
  exact Horrocks.polynomialRange_eq_top _ h h.property hW
    (projectedMulVec_mod_maximal B D hBD hD)

/-- Columnwise polynomial-part surjectivity produces a polynomial matrix
whose projected product is the identity. -/
theorem exists_right_projection [DecidableEq m]
    (B : Matrix m n (MonicFrac A)) (D : Matrix n m (MonicFrac A)) (hBD : B * D = 1)
    (hD : ∀ i j, D i j ∈ residuePolynomialSubring (A := A)) :
    ∃ H : Matrix n m A[X],
      (B * H.map (algebraMap A[X] (MonicFrac A))).map polynomialPart = 1 := by
  classical
  have hs := projectedMulVec_surjective B D hBD hD
  choose P hP using fun j : m => hs (fun i => (1 : Matrix m m A[X]) i j)
  refine ⟨fun i j => P j i, ?_⟩
  funext i j
  exact congrFun (hP j) i

end

end Decoupling.HorrocksProjection
