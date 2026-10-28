import Decoupling.HighDim.ExtValuesAlternating

/-!
# Laurent lattice paths in arbitrary integer directions

Source: Appendix B.2, the signed staircase chains P_a. A path is built
from unit steps by concatenation and reversal. In particular negative
coordinates are included, and coefficient augmentation counts signed
steps in each direction.
-/

namespace Decoupling.HighDim.KoszulLattice

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K] {D : ℕ}

/-- Coefficients of a finite Laurent one-chain with the specified boundary
and signed step counts. -/
def HasPath (a : Translation D) : Prop :=
  ∃ q : Fin D → Laurent K D,
    (∑ i, q i * difference K i) = monomial K a - 1 ∧
      ∀ i, augmentation (q i) = (a i : K)

theorem hasPath_zero : HasPath K (0 : Translation D) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

theorem hasPath_add {a b : Translation D} (ha : HasPath K a) (hb : HasPath K b) :
    HasPath K (a + b) := by
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨v, hv, hva⟩ := hb
  refine ⟨fun i => u i + monomial K a * v i, ?_, ?_⟩
  · simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hu, hv]
    rw [← monomial_mul]
    ring
  · intro i
    simp [hua, hva]

theorem hasPath_neg {a : Translation D} (ha : HasPath K a) : HasPath K (-a) := by
  obtain ⟨u, hu, hua⟩ := ha
  refine ⟨fun i => -(monomial K (-a) * u i), ?_, ?_⟩
  · simp only [neg_mul, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, hu,
      mul_sub, monomial_neg_mul, mul_one]
    ring
  · intro i
    simp [hua]

theorem hasPath_basis (i : Fin D) : HasPath K (translationBasis i) := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · simp [difference, coordinate, Pi.single_apply, Finset.sum_ite_eq']
  · intro j
    by_cases h : j = i
    · subst j; simp [translationBasis]
    · simp [translationBasis, Pi.single_eq_of_ne h]

/-- Every integer translation has a signed lattice path. This includes
arbitrary negative entries and requires no axis-alignment assumption. -/
theorem hasPath (a : Translation D) : HasPath K a := by
  let H : AddSubgroup (Translation D) :=
    { carrier := {a | HasPath K a}
      zero_mem' := hasPath_zero K
      add_mem' := hasPath_add K
      neg_mem' := hasPath_neg K }
  have hb (i : Fin D) : translationBasis i ∈ H := hasPath_basis K i
  have ha : ∑ i : Fin D, (a i) • translationBasis i ∈ H :=
    H.sum_mem fun i _ => H.zsmul_mem (hb i) (a i)
  have heq : ∑ i : Fin D, (a i) • translationBasis i = a := by
    funext j
    simp [translationBasis, Finset.sum_apply, Pi.single_apply, mul_ite,
      zsmul_eq_mul]
  change a ∈ H
  rwa [heq] at ha

/-- A proved choice of actual Laurent path coefficients. -/
def pathCoefficients (a : Translation D) : Fin D → Laurent K D :=
  (hasPath K a).choose

theorem pathCoefficients_boundary (a : Translation D) :
    (∑ i, pathCoefficients K a i * difference K i) = monomial K a - 1 :=
  (hasPath K a).choose_spec.1

@[simp] theorem augmentation_pathCoefficients (a : Translation D) (i : Fin D) :
    augmentation (pathCoefficients K a i) = (a i : K) :=
  (hasPath K a).choose_spec.2 i

end
end Decoupling.HighDim.KoszulLattice
