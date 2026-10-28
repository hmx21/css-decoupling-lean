import Decoupling.HighDim.ToricHodge

/-!
# The signed Hodge pairing intertwines the actual Koszul differentials

The proof sums over the proved bijection of actual complementary boundary
incidences. It is valid over every commutative ring with arbitrary weights.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
attribute [local instance] Classical.propDecidable
variable (A : Type*) [CommRing A] {D k l : ℕ} (w : Fin D → A)

theorem signed_incidence_sum (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (J : Cell D (l + 1)) :
    (∑ a : Fin (k + 1), if complement (by omega : k + (l + 1) = D) (face I a) = J
      then (-1 : A) ^ a.val * w (I a) * orientation A (face I a) else 0) =
    ∑ b : Fin (l + 1), if complement h I = face J b
      then (-1 : A) ^ b.val * w (J b) * orientation A I else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  let e := incidenceEquiv h I J
  let φ (a : Fin (k + 1)) (ha : a ∈ Finset.univ.filter
      (fun a => complement (by omega : k + (l + 1) = D) (face I a) = J)) :=
    (e ⟨a, (Finset.mem_filter.mp ha).2⟩).val
  apply Finset.sum_bij φ
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (e ⟨a, (Finset.mem_filter.mp ha).2⟩).property.symm⟩
  · intro a ha a' ha' he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  · intro b hb
    obtain ⟨a, ha⟩ := e.surjective ⟨b, (Finset.mem_filter.mp hb).2.symm⟩
    exact ⟨a.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property⟩,
      congrArg Subtype.val ha⟩
  · intro a ha
    have hJ := (Finset.mem_filter.mp ha).2
    change (-1 : A) ^ a.val * w (I a) * orientation A (face I a) =
      (-1 : A) ^ (dualIndex h I a).val * w (J (dualIndex h I a)) * orientation A I
    have hp : J (dualIndex h I a) = I a := by
      simpa only [hJ] using dualIndex_apply h I a
    rw [hp]
    have hs := orientation_incidence A h I a (dualIndex h I a) (dualIndex_apply h I a)
    calc
      _ = w (I a) * ((-1 : A) ^ a.val * orientation A (face I a)) := by ring
      _ = w (I a) * ((-1 : A) ^ (dualIndex h I a).val * orientation A I) := by rw [hs]
      _ = _ := by ring

theorem duality_boundary_basis (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (J : Cell D (l + 1)) :
    duality A (by omega : k + (l + 1) = D)
      (boundary A w k (Finsupp.single I 1)) (Finsupp.single J 1) =
    duality A h (Finsupp.single I 1) (boundary A w l (Finsupp.single J 1)) := by
  have hs (n : ℕ) (L : Cell D (n + 1)) :
      boundary A w n (Finsupp.single L 1) =
        ∑ i : Fin (n + 1), ((-1 : A) ^ i.val * w (L i)) • Finsupp.single (face L i) 1 := by
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using boundary_basis A w n L
  rw [hs k I, hs l J]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    duality_single_single, mul_ite, mul_zero]
  exact signed_incidence_sum A w h I J

/-- A genuine equality of linear maps into the genuine module dual. -/
theorem duality_boundary (h : k + 1 + l = D) :
    (duality A (by omega : k + (l + 1) = D)).toLinearMap.comp (boundary A w k).hom =
      (boundary A w l).hom.dualMap.comp (duality A h).toLinearMap := by
  apply (Finsupp.basisSingleOne : Module.Basis (Cell D (k + 1)) A (Term A D (k + 1))).ext
  intro I
  apply (Finsupp.basisSingleOne : Module.Basis (Cell D (l + 1)) A (Term A D (l + 1))).ext
  intro J
  exact duality_boundary_basis A w h I J

end
end Decoupling.HighDim.Toric.Hodge
