import Decoupling.LaurentRegular
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The actual retained ring after doubling

The paper's `S = 𝔽₂[x±²,y±²,z±²] ⊆ R` is defined as the image of the
injective exponent-doubling ring homomorphism. Its inclusion and the elements
X=x², Y=y², Z=z² are concrete. This removes the coefficient-embedding hypotheses
from the generic Koszul comparison identities. Freeness of rank eight over S
is a separate assertion, not implicit in these definitions.
-/

namespace Decoupling.RetainedRing

noncomputable section

/-- Double all integer translation exponents. -/
def doubleExponent : Translation →+ Translation where
  toFun a i := 2 * a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]

theorem doubleExponent_injective : Function.Injective doubleExponent := by
  intro a b h
  funext i
  have hi := congrFun h i
  change 2 * a i = 2 * b i at hi
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) hi

/-- The ring embedding sending (x,y,z) to (x²,y²,z²). -/
def embed : R →+* R := AddMonoidAlgebra.mapDomainRingHom (ZMod 2) doubleExponent

theorem embed_injective : Function.Injective embed :=
  AddMonoidAlgebra.mapDomain_injective doubleExponent_injective

@[simp] theorem embed_monomial (a : Translation) :
    embed (monomial a) = monomial (doubleExponent a) := by
  simp [embed, monomial]

theorem embed_monomial_square (a : Translation) : embed (monomial a) = monomial a ^ 2 := by
  rw [embed_monomial, pow_two, monomial_mul]
  congr 1
  funext i
  simp [doubleExponent, two_mul]

/-- The retained Laurent subring, as a literal subring of R. -/
def retained : Subring R := embed.range

abbrev S := retained

instance : Algebra S R := retained.subtype.toAlgebra

/-- The retained subring is itself a Laurent polynomial ring with renamed variables. -/
def renameEquiv : R ≃+* S :=
  RingEquiv.ofBijective embed.rangeRestrict
    ⟨fun _ _ h => embed_injective (congrArg Subtype.val h), embed.rangeRestrict_surjective⟩

instance : CharP S 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by
    apply Subtype.ext
    change (2 : R) = 0
    exact CharTwo.two_eq_zero)

def X : S := ⟨embed x, ⟨x, rfl⟩⟩
def Y : S := ⟨embed y, ⟨y, rfl⟩⟩
def Z : S := ⟨embed z, ⟨z, rfl⟩⟩

@[simp] theorem rename_x : renameEquiv x = X := rfl
@[simp] theorem rename_y : renameEquiv y = Y := rfl
@[simp] theorem rename_z : renameEquiv z = Z := rfl
@[simp] theorem rename_u : renameEquiv u = X - 1 := by simp [u]
@[simp] theorem rename_v : renameEquiv v = Y - 1 := by simp [v]
@[simp] theorem rename_w : renameEquiv w = Z - 1 := by simp [w]

/-- Regularity also holds over the actual retained ring, without extra assumptions. -/
theorem retained_regularTriple : Koszul.RegularTriple (X - 1) (Y - 1) (Z - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨a, rfl⟩ := renameEquiv.surjective a
    obtain ⟨b, rfl⟩ := renameEquiv.surjective b
    apply congrArg renameEquiv
    apply laurent_regularTriple.u_injective
    apply renameEquiv.injective
    simpa only [map_mul, rename_u] using h
  · intro a b h
    obtain ⟨a, rfl⟩ := renameEquiv.surjective a
    obtain ⟨b, rfl⟩ := renameEquiv.surjective b
    have hab : v * a = u * b := renameEquiv.injective (by simpa only [map_mul, rename_u, rename_v] using h)
    obtain ⟨r, hr⟩ := laurent_regularTriple.v_mod_u a b hab
    exact ⟨renameEquiv r, by simp [hr]⟩
  · intro a b c h
    obtain ⟨a, rfl⟩ := renameEquiv.surjective a
    obtain ⟨b, rfl⟩ := renameEquiv.surjective b
    obtain ⟨c, rfl⟩ := renameEquiv.surjective c
    have hab : w * a = u * b + v * c := renameEquiv.injective
      (by simpa only [map_mul, map_add, rename_u, rename_v, rename_w] using h)
    obtain ⟨r, s, hr⟩ := laurent_regularTriple.w_mod_uv a b c hab
    exact ⟨renameEquiv r, renameEquiv s, by simp [hr]⟩

@[simp] theorem inclusion_X : algebraMap S R X = x ^ 2 := embed_monomial_square _
@[simp] theorem inclusion_Y : algebraMap S R Y = y ^ 2 := embed_monomial_square _
@[simp] theorem inclusion_Z : algebraMap S R Z = z ^ 2 := embed_monomial_square _

@[simp] theorem inclusion_X_sub_one : algebraMap S R (X - 1) = u ^ 2 := by
  simp [u, CharTwo.sub_eq_add, add_sq, CharTwo.two_eq_zero]

@[simp] theorem inclusion_Y_sub_one : algebraMap S R (Y - 1) = v ^ 2 := by
  simp [v, CharTwo.sub_eq_add, add_sq, CharTwo.two_eq_zero]

@[simp] theorem inclusion_Z_sub_one : algebraMap S R (Z - 1) = w ^ 2 := by
  simp [w, CharTwo.sub_eq_add, add_sq, CharTwo.two_eq_zero]

open Matrix

/-- Degree one of the actual S-linear comparison. -/
theorem comparison₁ (a : Fin 3 → S) :
    Koszul.d₁ u v w *ᵥ Koszul.χ₁Over S u v w a =
      Koszul.χ₀Over S (Koszul.d₁ (X - 1) (Y - 1) (Z - 1) *ᵥ a) :=
  Koszul.comparison₁_over S u v w (X - 1) (Y - 1) (Z - 1)
    inclusion_X_sub_one inclusion_Y_sub_one inclusion_Z_sub_one a

/-- Degree two of the actual S-linear comparison. -/
theorem comparison₂ (a : Fin 3 → S) :
    Koszul.d₂ u v w *ᵥ Koszul.χ₂Over S u v w a =
      Koszul.χ₁Over S u v w (Koszul.d₂ (X - 1) (Y - 1) (Z - 1) *ᵥ a) :=
  Koszul.comparison₂_over S u v w (X - 1) (Y - 1) (Z - 1)
    inclusion_X_sub_one inclusion_Y_sub_one inclusion_Z_sub_one a

/-- Degree three of the actual S-linear comparison. -/
theorem comparison₃ (a : Fin 1 → S) :
    Koszul.d₃ u v w *ᵥ Koszul.χ₃Over S u v w a =
      Koszul.χ₂Over S u v w (Koszul.d₃ (X - 1) (Y - 1) (Z - 1) *ᵥ a) :=
  Koszul.comparison₃_over S u v w (X - 1) (Y - 1) (Z - 1)
    inclusion_X_sub_one inclusion_Y_sub_one inclusion_Z_sub_one a

end
end Decoupling.RetainedRing
