import Decoupling.HighDim.KoszulLatticeExterior
import Decoupling.HighDim.ExtValuesFunctor
import Decoupling.HighDim.MinimalLatticeContraction

/-!
# Actual Koszul cochain contractions for native Yoneda detection

The degree-one operators are contractions in the genuine free Koszul
resolution, and their anticommutation is proved with all signs retained.
-/

namespace Decoupling.HighDim.YonedaDetection
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul KoszulLattice Toric.Hodge CochainComplex.HomComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem boundary_anticommute (R : Type*) [CommRing R] {D : ℕ}
    (w v : Fin D → R) (n : ℕ) :
    boundary R v (n + 1) ≫ boundary R w n +
      boundary R w (n + 1) ≫ boundary R v n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply termExterior_injective R D n
  change termExterior R D n (boundary R w n (boundary R v (n + 1) x) +
    boundary R v n (boundary R w (n + 1) x)) = termExterior R D n 0
  simp only [map_add, map_zero]
  rw [termExterior_boundary R D w n, termExterior_boundary R D v n,
    termExterior_boundary R D v (n + 1), termExterior_boundary R D w (n + 1)]
  rw [CliffordAlgebra.contractLeft_comm]
  simp

theorem exists_coface {D n : ℕ} (I : Cell D n) (hnD : n < D) :
    ∃ (J : Cell D (n + 1)) (a : Fin (n + 1)), face J a = I := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := directions I) (t := Finset.univ) (by simpa using hnD)
  have hc : (insert x (directions I)).card = n + 1 := by simp [hx]
  let J : Cell D (n + 1) := (insert x (directions I)).orderEmbOfFin hc
  have hJ : directions J = insert x (directions I) := Finset.map_orderEmbOfFin_univ _ _
  obtain ⟨a, ha⟩ := (mem_directions J x).mp (hJ ▸ Finset.mem_insert_self x (directions I))
  refine ⟨J, a, directions_injective ?_⟩
  rw [directions_face, hJ, ha, Finset.erase_insert hx]

theorem coordinate_contraction_basis (R : Type*) [CommRing R] {D n : ℕ}
    (J : Cell D (n + 1)) (a : Fin (n + 1)) :
    boundary R (Pi.single (J a) 1) n (Finsupp.single J 1) =
      Finsupp.single (face J a) ((-1 : R) ^ a.val) := by
  rw [boundary_basis, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (J.injective.ne hb)]
  · simp

variable (K : Type) [Field K] (D : ℕ)

abbrev resolution := projectiveResolution K D
abbrev complex := (resolution K D).cochainComplex

def coordinateBoundary (a : Fin D) (n : ℕ) :
    (resolution K D).complex.X (n + 1) ⟶ (resolution K D).complex.X n :=
  boundary (Laurent K D) (Pi.single a 1) n

def contractionCochain (a : Fin D) : Cochain (complex K D) (complex K D) 1 :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    ((resolution K D).cochainComplexXIso p ((-q).toNat + 1) (by omega)).hom ≫
      coordinateBoundary K D a (-q).toNat ≫
        ((resolution K D).cochainComplexXIso q (-q).toNat (by omega)).inv
    else 0)

theorem contractionCochain_v (a : Fin D) (n : ℕ) :
    (contractionCochain K D a).v (-(n + 1 : ℕ)) (-(n : ℤ)) (by omega) =
      ((resolution K D).cochainComplexXIso (-(n + 1 : ℕ)) (n + 1) rfl).hom ≫
        coordinateBoundary K D a n ≫
          ((resolution K D).cochainComplexXIso (-(n : ℤ)) n rfl).inv := by
  dsimp only [contractionCochain, Cochain.mk_v]
  simp only [show (-(n : ℤ)) ≤ 0 by omega, dite_true]
  have he (p q : ℤ) (i j : ℕ) (hi : -(i : ℤ) = q) (hj : -(j : ℤ) = q)
      (hip : -((i + 1 : ℕ) : ℤ) = p) (hjp : -((j + 1 : ℕ) : ℤ) = p) :
      ((resolution K D).cochainComplexXIso p (i + 1) hip).hom ≫
        coordinateBoundary K D a i ≫ ((resolution K D).cochainComplexXIso q i hi).inv =
      ((resolution K D).cochainComplexXIso p (j + 1) hjp).hom ≫
        coordinateBoundary K D a j ≫ ((resolution K D).cochainComplexXIso q j hj).inv := by
    have : i = j := by omega
    subst j
    rfl
  exact he _ _ _ _ _ _ _ _

theorem resolution_d (n : ℕ) : (resolution K D).complex.d (n + 1) n =
    boundary (Laurent K D) (difference K) n := complex_d _ _ _

theorem contractionCochain_cocycle (a : Fin D) : δ 1 2 (contractionCochain K D a) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -q)
    have hqn : q = -(n : ℤ) := by omega
    have hpn : p = -((n + 2 : ℕ) : ℤ) := by omega
    subst p
    subst q
    rw [δ_v 1 2 rfl _ _ _ _ (-(n + 1 : ℕ)) (-(n + 1 : ℕ)) (by omega) (by omega),
      contractionCochain_v, contractionCochain_v,
      (resolution K D).cochainComplex_d _ _ (n + 1) n rfl rfl,
      (resolution K D).cochainComplex_d _ _ (n + 2) (n + 1) rfl rfl]
    simp only [Cochain.zero_v, show (2 : ℤ).negOnePow = 1 from rfl,
      one_smul, Category.assoc, Iso.inv_hom_id_assoc, resolution_d, coordinateBoundary]
    have he := congrArg (fun f =>
      ((resolution K D).cochainComplexXIso (-((n + 2 : ℕ) : ℤ)) (n + 2) rfl).hom ≫ f ≫
        ((resolution K D).cochainComplexXIso (-(n : ℤ)) n rfl).inv)
      (boundary_anticommute (Laurent K D) (difference K) (Pi.single a 1) n)
    simpa only [comp_add, add_comp, Category.assoc, comp_zero, zero_comp] using he
  · exact ((complex K D).isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def contractionCocycle (a : Fin D) : Cocycle (complex K D) (complex K D) 1 :=
  Cocycle.mk (contractionCochain K D a) 2 rfl (contractionCochain_cocycle K D a)

end
end Decoupling.HighDim.YonedaDetection
