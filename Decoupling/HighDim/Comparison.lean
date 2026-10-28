import Decoupling.HighDim.Stabilization
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Comparison maps from an actual check-cokernel isomorphism

This module proves the lifting step in `drafts/main.tex`, Section IV.B.
For finite-free differentials `dC : C⁰ → C¹` and `dT : T⁰ → T¹`,
an isomorphism of the actual quotients by their ranges produces all six
comparison maps and all four identities needed by signed stabilization.

The final theorem `exists_comparisonData` assumes only a linear equivalence
between those quotients; comparison identities are conclusions. The proof
uses projectivity of finite free modules, with classical (nonalgorithmic)
choices of lifts. The upstream derivation of a stable cokernel isomorphism
from a split profile is not asserted here.
-/

namespace Decoupling.HighDim.Comparison

open Matrix

section Lifting

variable {R : Type*} [CommRing R]
  {P M N : Type*}
  [AddCommGroup P] [Module R P] [Module.Projective R P]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A map from a projective module lifts through `f` when its range is
contained in the range of `f`. -/
theorem exists_lift_of_range_le (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (h : LinearMap.range g ≤ LinearMap.range f) :
    ∃ l : P →ₗ[R] M, f.comp l = g := by
  let g' := g.codRestrict (LinearMap.range f) fun p => h ⟨p, rfl⟩
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property f.rangeRestrict g' f.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext p
  exact congrArg Subtype.val (DFunLike.congr_fun hl p)

/-- Exactness gives a lift of a map with zero composite with the augmentation. -/
theorem exists_lift_of_comp_eq_zero
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (d : M →ₗ[R] N) (pi : N →ₗ[R] Q) (g : P →ₗ[R] N)
    (hexact : LinearMap.range d = LinearMap.ker pi) (hzero : pi.comp g = 0) :
    ∃ l : P →ₗ[R] M, d.comp l = g := by
  apply exists_lift_of_range_le d g
  rw [hexact]
  rintro _ ⟨p, rfl⟩
  exact DFunLike.congr_fun hzero p

end Lifting

section Comparison

variable {R : Type*} [CommRing R]
  {C₀ C₁ T₀ T₁ : Type*}
  [Fintype C₀] [Fintype C₁] [Fintype T₀] [Fintype T₁]
  [DecidableEq C₀] [DecidableEq C₁] [DecidableEq T₀] [DecidableEq T₁]

/-- General augmented-presentation form of the lifting argument. Both
augmentations are required to be surjective and exact at degree one.
Specializing to the actual quotient maps discharges all these conditions. -/
theorem exists_comparisonData_of_presentations
    {NC NT : Type*} [AddCommGroup NC] [Module R NC]
    [AddCommGroup NT] [Module R NT]
    (dC : Matrix C₁ C₀ R) (dT : Matrix T₁ T₀ R)
    (piC : (C₁ → R) →ₗ[R] NC) (piT : (T₁ → R) →ₗ[R] NT)
    (surjectiveC : Function.Surjective piC) (surjectiveT : Function.Surjective piT)
    (exactC : LinearMap.range dC.mulVecLin = LinearMap.ker piC)
    (exactT : LinearMap.range dT.mulVecLin = LinearMap.ker piT)
    (beta : NT ≃ₗ[R] NC) :
    ∃ c : Stabilization.ComparisonData R C₀ C₁ T₀ T₁,
      c.dC = dC ∧ c.dT = dT ∧
      piC.comp c.phi1.mulVecLin = beta.toLinearMap.comp piT ∧
      piT.comp c.psi1.mulVecLin = beta.symm.toLinearMap.comp piC := by
  obtain ⟨phi1, hphi1⟩ :=
    Module.projective_lifting_property piC (beta.toLinearMap.comp piT) surjectiveC
  obtain ⟨psi1, hpsi1⟩ :=
    Module.projective_lifting_property piT (beta.symm.toLinearMap.comp piC) surjectiveT
  have hphi (v : T₁ → R) : piC (phi1 v) = beta (piT v) :=
    DFunLike.congr_fun hphi1 v
  have hpsi (v : C₁ → R) : piT (psi1 v) = beta.symm (piC v) :=
    DFunLike.congr_fun hpsi1 v
  have hdC (v : C₀ → R) : piC (dC.mulVecLin v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactC]
    exact ⟨v, rfl⟩
  have hdT (v : T₀ → R) : piT (dT.mulVecLin v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactT]
    exact ⟨v, rfl⟩
  obtain ⟨phi0, hphi0⟩ :=
    exists_lift_of_comp_eq_zero dC.mulVecLin piC (phi1.comp dT.mulVecLin) exactC
      (by ext v; simp only [LinearMap.comp_apply, hphi, hdT, map_zero,
        LinearMap.zero_apply])
  obtain ⟨psi0, hpsi0⟩ :=
    exists_lift_of_comp_eq_zero dT.mulVecLin piT (psi1.comp dC.mulVecLin) exactT
      (by ext v; simp only [LinearMap.comp_apply, hpsi, hdC, map_zero,
        LinearMap.zero_apply])
  obtain ⟨etaC, hetaC⟩ :=
    exists_lift_of_comp_eq_zero dC.mulVecLin piC (LinearMap.id - phi1.comp psi1) exactC
      (by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          map_sub, hphi, hpsi, beta.apply_symm_apply, sub_self, LinearMap.zero_apply])
  obtain ⟨etaT, hetaT⟩ :=
    exists_lift_of_comp_eq_zero dT.mulVecLin piT (LinearMap.id - psi1.comp phi1) exactT
      (by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          map_sub, hpsi, hphi, beta.symm_apply_apply, sub_self, LinearMap.zero_apply])
  refine ⟨{
    dC := dC
    dT := dT
    phi0 := LinearMap.toMatrix' phi0
    psi0 := LinearMap.toMatrix' psi0
    phi1 := LinearMap.toMatrix' phi1
    psi1 := LinearMap.toMatrix' psi1
    etaC := LinearMap.toMatrix' etaC
    etaT := LinearMap.toMatrix' etaT
    forward := ?_
    backward := ?_
    homotopyC := ?_
    homotopyT := ?_
  }, rfl, rfl, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply' dC, Matrix.toLin'_apply' dT] using hphi0
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply' dC, Matrix.toLin'_apply' dT] using hpsi0
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_sub,
      Matrix.toLin'_one, Matrix.toLin'_apply' dC] using hetaC
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_sub,
      Matrix.toLin'_one, Matrix.toLin'_apply' dT] using hetaT
  · change piC.comp (Matrix.toLin' (LinearMap.toMatrix' phi1)) = _
    simpa only [Matrix.toLin'_toMatrix'] using hphi1
  · change piT.comp (Matrix.toLin' (LinearMap.toMatrix' psi1)) = _
    simpa only [Matrix.toLin'_toMatrix'] using hpsi1

/-- The actual check cokernel, defined as the quotient by the differential's range. -/
abbrev CheckCokernel {I J : Type*} [Fintype J] (d : Matrix I J R) :=
  (I → R) ⧸ LinearMap.range d.mulVecLin

/-- Canonical quotient map to the actual check cokernel. -/
abbrev checkQuotient {I J : Type*} [Fintype J] (d : Matrix I J R) :
    (I → R) →ₗ[R] CheckCokernel d :=
  (LinearMap.range d.mulVecLin).mkQ

/-- An isomorphism of the actual check cokernels constructs all comparison
maps and signed homotopies. No comparison identities are assumed. The last
two equalities certify that the degree-one maps lift the supplied isomorphism
and its inverse, rather than merely some isomorphism. -/
theorem exists_comparisonData
    (dC : Matrix C₁ C₀ R) (dT : Matrix T₁ T₀ R)
    (beta : CheckCokernel dT ≃ₗ[R] CheckCokernel dC) :
    ∃ c : Stabilization.ComparisonData R C₀ C₁ T₀ T₁,
      c.dC = dC ∧ c.dT = dT ∧
      (checkQuotient dC).comp c.phi1.mulVecLin =
        beta.toLinearMap.comp (checkQuotient dT) ∧
      (checkQuotient dT).comp c.psi1.mulVecLin =
        beta.symm.toLinearMap.comp (checkQuotient dC) := by
  apply exists_comparisonData_of_presentations dC dT (checkQuotient dC)
    (checkQuotient dT) (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _)
    _ _ beta
  · exact (Submodule.ker_mkQ _).symm
  · exact (Submodule.ker_mkQ _).symm

end Comparison

end Decoupling.HighDim.Comparison
