import Decoupling.HighDim.EffectiveLinearConstantBasis
import Decoupling.HighDim.HermannBounds

/-!
# Transport of actual polynomial kernel generation

All coordinate changes here are genuine ring/algebra equivalences. The
span arguments transport their actual scalars as well as their vectors.
No claim of bounded generation is made by these auxiliary implications.
-/

namespace Decoupling.HighDim.Hermann

open Matrix MvPolynomial EffectiveLinear
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K] {N m n r : ℕ}

/-- Apply an actual coefficient-ring homomorphism componentwise. -/
def mapVector {S T : Type*} (f : S → T) {ι : Type*} (y : ι → S) : ι → T :=
  fun j => f (y j)

@[simp] theorem mapVector_zero {S T : Type*} [Semiring S] [Semiring T]
    (f : S →+* T) {ι : Type*} : mapVector f (0 : ι → S) = 0 := by
  funext i
  exact map_zero f

theorem mapVector_mulVec {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (A : Matrix (Fin m) (Fin n) S) (y : Fin n → S) :
    mapVector f (A *ᵥ y) = A.map f *ᵥ mapVector f y := by
  classical
  funext i
  simp [mapVector, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Actual componentwise ring maps carry a polynomial span into any
submodule containing the images of its generators. -/
theorem mapVector_span_mem {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) {ι : Type*} (G : Set (ι → S)) (P : Submodule T (ι → T))
    (hG : ∀ y ∈ G, mapVector φ y ∈ P) (y : ι → S)
    (hy : y ∈ Submodule.span S G) : mapVector φ y ∈ P := by
  refine Submodule.span_induction hG ?_ ?_ ?_ hy
  · rw [mapVector_zero]
    exact P.zero_mem
  · intro x z hx hz ihx ihz
    have he : mapVector φ (x+z) = mapVector φ x + mapVector φ z := by
      funext i
      exact map_add φ _ _
    rw [he]
    exact P.add_mem ihx ihz
  · intro a x hx ihx
    have he : mapVector φ (a • x) = φ a • mapVector φ x := by
      funext i
      exact map_mul φ _ _
    rw [he]
    exact P.smul_mem _ ihx

/-- A genuine ring equivalence preserves the actual kernel equation. -/
theorem mapVector_kernel_iff {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (A : Matrix (Fin m) (Fin n) S) (y : Fin n → S) :
    A.map e *ᵥ mapVector e y = 0 ↔ A *ᵥ y = 0 := by
  change A.map e.toRingHom *ᵥ mapVector e.toRingHom y = 0 ↔ A *ᵥ y = 0
  rw [← mapVector_mulVec e.toRingHom]
  constructor
  · intro h
    funext i
    apply e.injective
    have hi := congrFun h i
    change e ((A *ᵥ y) i) = 0 at hi
    exact hi.trans e.map_zero.symm
  · intro h
    rw [h, mapVector_zero]

/-- Enlargement of a proved degree budget keeps genuine kernel generation. -/
theorem kernel_generation_mono
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) {B C : ℕ} (hBC : B ≤ C)
    (h : LinearMap.ker A.mulVecLin = Submodule.span _ (degreeKernel A B)) :
    LinearMap.ker A.mulVecLin = Submodule.span _ (degreeKernel A C) := by
  apply le_antisymm
  · rw [h]
    apply Submodule.span_mono
    intro y hy
    exact ⟨hy.1, fun j => (hy.2 j).trans hBC⟩
  · exact Submodule.span_le.mpr (fun _ hy => hy.1)

/-- Retaining an equivalent actual kernel retains its degree-bounded span. -/
theorem kernel_generation_of_kernel_iff
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (B : Matrix (Fin r) (Fin n) (MvPolynomial (Fin N) K))
    (hker : ∀ y, A *ᵥ y = 0 ↔ B *ᵥ y = 0) (b : ℕ)
    (hB : LinearMap.ker B.mulVecLin = Submodule.span _ (degreeKernel B b)) :
    LinearMap.ker A.mulVecLin = Submodule.span _ (degreeKernel A b) := by
  have hk : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext y
    exact hker y
  have hs : degreeKernel A b = degreeKernel B b := by
    ext y
    exact and_congr_left (fun _ => hker y)
  rw [hk, hs, hB]

/-- A degree-preserving polynomial automorphism transports a proved bound
back to the original matrix, including the actual polynomial span scalars. -/
theorem kernel_generation_of_coordinates
    (e : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    (hdegree : ∀ P, (e P).totalDegree = P.totalDegree)
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) (B : ℕ)
    (hgen : LinearMap.ker (A.map e).mulVecLin =
      Submodule.span _ (degreeKernel (A.map e) B)) :
    LinearMap.ker A.mulVecLin = Submodule.span _ (degreeKernel A B) := by
  classical
  have hspan : ∀ z : Fin n → MvPolynomial (Fin N) K,
      z ∈ Submodule.span (MvPolynomial (Fin N) K) (degreeKernel (A.map e) B) →
      mapVector e.symm z ∈ Submodule.span (MvPolynomial (Fin N) K) (degreeKernel A B) := by
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro x hx
      apply Submodule.subset_span
      constructor
      · apply (mapVector_kernel_iff e.toRingEquiv A (mapVector e.symm x)).mp
        change A.map e *ᵥ (fun j => e (e.symm (x j))) = 0
        simpa only [AlgEquiv.apply_symm_apply] using hx.1
      · intro j
        have hd := hdegree (e.symm (x j))
        rw [AlgEquiv.apply_symm_apply] at hd
        exact hd.symm.le.trans (hx.2 j)
    · have hz : mapVector e.symm (0 : Fin n → MvPolynomial (Fin N) K) = 0 := by
        funext i
        exact map_zero e.symm
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy ihx ihy
      have he : mapVector e.symm (x+y) = mapVector e.symm x + mapVector e.symm y := by
        funext i
        exact map_add e.symm _ _
      rw [he]
      exact Submodule.add_mem _ ihx ihy
    · intro c x hx ihx
      have he : mapVector e.symm (c • x) = e.symm c • mapVector e.symm x := by
        funext i
        exact map_mul e.symm _ _
      rw [he]
      exact Submodule.smul_mem _ _ ihx
  apply le_antisymm
  · intro y hy
    have hz : mapVector e y ∈ Submodule.span (MvPolynomial (Fin N) K) (degreeKernel (A.map e) B) := by
      rw [← hgen]
      exact (mapVector_kernel_iff e.toRingEquiv A y).mpr hy
    have he : mapVector e.symm (mapVector e y) = y := by
      funext j
      exact e.symm_apply_apply (y j)
    have hh := hspan _ hz
    rw [he] at hh
    exact hh
  · exact Submodule.span_le.mpr (fun _ hy => hy.1)

end
end Decoupling.HighDim.Hermann
