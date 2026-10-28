import Decoupling.HighDim.EffectiveLinearCoordinates

/-!
# Explicit coefficient entries of the finite bounded polynomial system

These identities connect the abstract finite linear coordinates to a direct
coefficient lookup implementation. They introduce no choices depending on the
field entries. The box exponent equivalence can be used to enumerate the rows
and columns by tuples of bounded natural numbers.
-/

namespace Decoupling.HighDim.EffectiveLinear
open MvPolynomial Matrix
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [CommRing K] (N : ℕ)

@[simp] theorem boxCoordinates_apply (b : ℕ) (P : BoxPolynomial K N b)
    (a : BoxExponent N b) : boxCoordinates K N b P a = P.val.coeff a.val := rfl

/-- The actual monomial belonging to the bounded support space. -/
def boxedMonomial (b : ℕ) (a : BoxExponent N b) : BoxPolynomial K N b :=
  ⟨MvPolynomial.monomial a.val 1,
    (MvPolynomial.monomial_mem_restrictSupport K).mpr (Or.inl a.property)⟩

@[simp] theorem boxCoordinates_boxedMonomial (b : ℕ) (a : BoxExponent N b) :
    boxCoordinates K N b (boxedMonomial K N b a) = Pi.single a 1 := by
  classical
  funext t
  rw [boxCoordinates_apply]
  change (MvPolynomial.monomial a.val (1 : K)).coeff t.val = (Pi.single a (1 : K) : BoxExponent N b → K) t
  rw [MvPolynomial.coeff_monomial, Pi.single_apply]
  by_cases ht : t = a
  · subst t
    simp
  · have hv : a.val ≠ t.val := fun h => ht (Subtype.ext h.symm)
    simp [ht, hv]

/-- A coefficient standard basis vector decodes to the expected actual monomial. -/
theorem vectorCoordinates_symm_single (n b : ℕ) (j : Fin n × BoxExponent N b) :
    (vectorCoordinates K N n b).symm (Pi.single j 1) =
      fun k => if k = j.1 then boxedMonomial K N b j.2 else 0 := by
  classical
  apply (vectorCoordinates K N n b).injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  change (Pi.single j (1 : K) : (Fin n × BoxExponent N b) → K) i = boxCoordinates K N b
    (if i.1 = j.1 then boxedMonomial K N b j.2 else 0) i.2
  by_cases hi : i.1 = j.1
  · simp only [hi, ite_true]
    rw [boxCoordinates_boxedMonomial]
    simp [Pi.single_apply, Prod.ext_iff, hi]
  · simp only [hi, ite_false, map_zero, Pi.zero_apply]
    simp [Prod.ext_iff, hi]

variable {K N} {m n d : ℕ}

@[simp] theorem vectorCoordinates_apply (n b : ℕ) (y : Fin n → BoxPolynomial K N b)
    (i : Fin n × BoxExponent N b) :
    vectorCoordinates K N n b y i = (y i.1).val.coeff i.2.val := rfl

@[simp] theorem boundedMul_apply_val
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d) (b : ℕ)
    (y : Fin n → BoxPolynomial K N b) (i : Fin m) :
    (boundedMul A hA b y i).val = (A *ᵥ (fun j => (y j).val)) i := rfl

/-- Actual finite matrix entries are coefficients of A_ij times one monomial. -/
theorem coefficientMatrix_entry
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d) (b : ℕ)
    (i : Fin m × BoxExponent N (d + b)) (j : Fin n × BoxExponent N b) :
    coefficientMatrix A hA b i j =
      (A i.1 j.1 * MvPolynomial.monomial j.2.val 1).coeff i.2.val := by
  classical
  rw [coefficientMatrix, LinearMap.toMatrix'_apply]
  change (vectorCoordinates K N m (d + b)
    (boundedMul A hA b ((vectorCoordinates K N n b).symm (Pi.single j 1)))) i = _
  rw [vectorCoordinates_symm_single]
  rw [vectorCoordinates_apply, boundedMul_apply_val]
  change (∑ k, A i.1 k *
    ((if k = j.1 then boxedMonomial K N b j.2 else 0) : BoxPolynomial K N b).val).coeff i.2.val = _
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j.1]
  · simp [boxedMonomial]
  · intro k hk hne
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The entry is a direct shifted coefficient lookup with a componentwise check. -/
theorem coefficientMatrix_entry_lookup
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d) (b : ℕ)
    (i : Fin m × BoxExponent N (d + b)) (j : Fin n × BoxExponent N b) :
    coefficientMatrix A hA b i j =
      if j.2.val ≤ i.2.val then (A i.1 j.1).coeff (i.2.val - j.2.val) else 0 := by
  rw [coefficientMatrix_entry, MvPolynomial.coeff_mul_monomial']
  simp

end
end Decoupling.HighDim.EffectiveLinear
