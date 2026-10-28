import Decoupling.HighDim.AlgorithmTwoFiniteComplexCoordinates

/-! # Encoding native graded maps in the finite total coordinates -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory HomologicalComplex Matrix
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C T : CochainComplex (ModuleCat R) ℤ} {n m : ℕ}

private theorem sum_smul_single (x : Fin m → R) :
    (∑ i, x i • Pi.single i (1 : R)) = x := by
  funext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]

/-- Matrix of an actual degree-s family, computed semantically on the
specified original total coordinate basis. -/
def familyMatrix (cT : Coordinates T m) (cC : Coordinates C n) (φ : ℤ → ℤ)
    (f : ∀ j, T.X j →ₗ[R] C.X (φ j)) : Matrix (Fin n) (Fin m) R :=
  fun i a => cC.embed (φ (cT.degree.get a)) (f (cT.degree.get a)
    (cT.project (cT.degree.get a) (Pi.single a 1))) i

theorem familyMatrix_homogeneous (cT : Coordinates T m) (cC : Coordinates C n) (φ : ℤ → ℤ)
    (f : ∀ j, T.X j →ₗ[R] C.X (φ j)) (s : ℤ) (hφ : ∀ j, φ j = j+s) :
    Homogeneous cT.degree cC.degree s (familyMatrix cT cC φ f) := by
  intro i a hi
  exact cC.embed_supported _ _ _ (by simpa [hφ] using hi)

theorem familyMatrix_mulVec (cT : Coordinates T m) (cC : Coordinates C n) (φ : ℤ → ℤ)
    (f : ∀ j, T.X j →ₗ[R] C.X (φ j)) (j : ℤ) (x : T.X j) :
    familyMatrix cT cC φ f *ᵥ cT.embed j x = cC.embed (φ j) (f j x) := by
  have hex : (∑ a, cT.embed j x a • cT.project j (Pi.single a 1)) = x := by
    simp_rw [← map_smul]
    rw [← map_sum]
    rw [sum_smul_single, cT.project_embed]
  conv_rhs => rw [← hex]
  rw [map_sum, map_sum]
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : (cT.degree.get a) = j
  · subst j
    simp only [familyMatrix, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
  · have hz := cT.embed_supported j x a ha
    simp [hz]

/-- Equality of maps on every graded component determines their total
matrix. In particular this is not only a test on some selected cocycles. -/
theorem matrix_ext (cT : Coordinates T m) (A B : Matrix (Fin n) (Fin m) R)
    (he : ∀ j x, A *ᵥ cT.embed j x = B *ᵥ cT.embed j x) : A = B := by
  funext i a
  have h := congrFun (he (cT.degree.get a) (cT.project (cT.degree.get a) (Pi.single a 1))) i
  have hs : cT.embed (cT.degree.get a) (cT.project (cT.degree.get a) (Pi.single a 1)) = Pi.single a 1 := by
    apply cT.project_supported
    intro b hb
    have hba : b ≠ a := by intro hba; subst b; exact hb rfl
    simp [hba]
  rw [hs] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h

/-- Total matrix of the actual native differential. -/
def differentialMatrix (c : Coordinates C n) : Matrix (Fin n) (Fin n) R :=
  familyMatrix c c (fun j => j+1) (fun j => (C.d j (j+1)).hom)

theorem differentialMatrix_represents (c : Coordinates C n) : c.RepresentsDifferential (differentialMatrix c) :=
  familyMatrix_mulVec c c (fun j => j+1) _

theorem differentialMatrix_homogeneous (c : Coordinates C n) :
    Homogeneous c.degree c.degree 1 (differentialMatrix c) := familyMatrix_homogeneous c c (fun j => j+1) _ 1 (fun _ => rfl)

/-- Total matrix of an actual cochain map. -/
def cochainMatrix (cT : Coordinates T m) (cC : Coordinates C n) (f : T ⟶ C) :
    Matrix (Fin n) (Fin m) R := familyMatrix cT cC id (fun j => (f.f j).hom)

theorem cochainMatrix_mulVec (cT : Coordinates T m) (cC : Coordinates C n) (f : T ⟶ C)
    (j : ℤ) (x : T.X j) : cochainMatrix cT cC f *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x) :=
  familyMatrix_mulVec cT cC id _ j x

theorem cochainMatrix_homogeneous (cT : Coordinates T m) (cC : Coordinates C n) (f : T ⟶ C) :
    Homogeneous cT.degree cC.degree 0 (cochainMatrix cT cC f) := familyMatrix_homogeneous cT cC id _ 0 (fun j => (add_zero j).symm)

theorem cochainMatrix_comm (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC) (f : T ⟶ C) :
    dC * cochainMatrix cT cC f = cochainMatrix cT cC f * dT := by
  apply matrix_ext cT
  intro j x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cochainMatrix_mulVec,
    hdC, hdT, cochainMatrix_mulVec]
  congr 1
  exact congrArg (fun g : T.X j ⟶ C.X (j+1) => g.hom x) (f.comm j (j+1))

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
