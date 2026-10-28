import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Selecting a genuine nonzero minor and retaining all kernel equations

The square block is selected from the original matrix entries. Its determinant
is nonzero, and its selected rows span the complete row space over the fraction
field. Thus reducing to these rows loses no homogeneous solutions over the
original integral domain. No rank or minor certificate is an input.
-/

namespace Decoupling.HighDim.Hermann
open Matrix Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A maximal independent collection of actual rows contains a nonsingular
square submatrix, with neither nonempty-index nor nonzero-matrix assumptions. -/
theorem exists_field_minor {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) :
    ∃ (r : ℕ) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
      (A.submatrix rows cols).det ≠ 0 ∧
      Submodule.span K (Set.range (fun i => A (rows i))) =
        Submodule.span K (Set.range A) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let r := Fintype.card κ
  let rows : Fin r ↪ Fin m := ⟨a ∘ (Fintype.equivFin κ).symm,
    ha.comp (Fintype.equivFin κ).symm.injective⟩
  let B : Matrix (Fin r) (Fin n) K := A.submatrix rows id
  have hrow : LinearIndependent K B.row :=
    hli.comp (Fintype.equivFin κ).symm (Fintype.equivFin κ).symm.injective
  have hspan' : Submodule.span K (Set.range (fun i => A (rows i))) =
      Submodule.span K (Set.range A) := by
    change Submodule.span K (Set.range ((A ∘ a) ∘ (Fintype.equivFin κ).symm)) = _
    rw [(Fintype.equivFin κ).symm.surjective.range_comp, hspan]
  obtain ⟨τ, b, hb, hspancol, hcol⟩ := exists_linearIndependent' K B.col
  let : Finite τ := Finite.of_injective b hb
  let : Fintype τ := Fintype.ofFinite τ
  have hcard : Fintype.card τ = r := by
    calc
      Fintype.card τ = Module.finrank K
          (Submodule.span K (Set.range (B.col ∘ b))) :=
        linearIndependent_iff_card_eq_finrank_span.mp hcol
      _ = B.rank := by rw [hspancol, Matrix.rank_eq_finrank_span_cols]
      _ = r := by simpa using hrow.rank_matrix
  let e : Fin r ≃ τ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let cols : Fin r ↪ Fin n := ⟨b ∘ e, hb.comp e.injective⟩
  have hminor : LinearIndependent K (A.submatrix rows cols).col := hcol.comp e e.injective
  refine ⟨r, rows, cols, ?_, hspan'⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hminor))

/-- A direct consequence needed for the degree recurrence. -/
theorem minor_size_le {r m : ℕ} (rows : Fin r ↪ Fin m) : r ≤ m := by
  simpa using Fintype.card_le_of_injective rows rows.injective

/-- Select a genuine minor over an arbitrary integral domain and prove that
its rows retain every homogeneous polynomial solution. -/
theorem exists_domain_minor {R : Type*} [CommRing R] [IsDomain R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    ∃ (r : ℕ) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n),
      (A.submatrix rows cols).det ≠ 0 ∧
      ∀ y : Fin n → R, A *ᵥ y = 0 ↔ A.submatrix rows id *ᵥ y = 0 := by
  let φ := algebraMap R (FractionRing R)
  obtain ⟨r, rows, cols, hdet, hspan⟩ := exists_field_minor (A.map φ)
  refine ⟨r, rows, cols, ?_, ?_⟩
  · change ((A.submatrix rows cols).map φ).det ≠ 0 at hdet
    have he := φ.map_det (A.submatrix rows cols)
    change φ ((A.submatrix rows cols).det) = ((A.submatrix rows cols).map φ).det at he
    rw [← he] at hdet
    exact fun he => hdet (by rw [he, map_zero])
  · intro y
    constructor
    · intro hy
      funext i
      exact congrFun hy (rows i)
    · intro hy
      have hrows (j : Fin r) : (A.map φ) (rows j) ⬝ᵥ (φ ∘ y) = 0 := by
        have h := congrArg φ (congrFun hy j)
        change φ (∑ k, A (rows j) k * y k) = φ 0 at h
        simpa only [map_sum, map_mul, map_zero, dotProduct, Matrix.map_apply,
          Function.comp_apply] using h
      funext i
      apply IsFractionRing.injective R (FractionRing R)
      change φ ((A *ᵥ y) i) = φ 0
      rw [map_zero, RingHom.map_mulVec]
      change (A.map φ) i ⬝ᵥ (φ ∘ y) = 0
      have hi : (A.map φ) i ∈ Submodule.span (FractionRing R)
          (Set.range (fun j => (A.map φ) (rows j))) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hi
      · rintro x ⟨j, rfl⟩
        exact hrows j
      · exact zero_dotProduct _
      · intro x z hx hz ihx ihz
        rw [add_dotProduct, ihx, ihz, add_zero]
      · intro a x hx ihx
        rw [smul_dotProduct, ihx, smul_zero]

/-- Once solvability is known, retaining an equivalent kernel retains the
entire inhomogeneous solution set, not merely its existence. -/
theorem row_solution_equivalence {R : Type*} [CommRing R] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (rows : Fin r ↪ Fin m)
    (hker : ∀ y, A *ᵥ y = 0 ↔ A.submatrix rows id *ᵥ y = 0)
    (b : Fin m → R) (y₀ : Fin n → R) (hy₀ : A *ᵥ y₀ = b) (y : Fin n → R) :
    A *ᵥ y = b ↔ A.submatrix rows id *ᵥ y = b ∘ rows := by
  have h₀ : A.submatrix rows id *ᵥ y₀ = b ∘ rows :=
    funext fun i => congrFun hy₀ (rows i)
  rw [← hy₀, ← sub_eq_zero, ← Matrix.mulVec_sub, hker,
    Matrix.mulVec_sub, sub_eq_zero, h₀, hy₀]

end
end Decoupling.HighDim.Hermann
