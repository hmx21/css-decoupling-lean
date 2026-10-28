import Decoupling.Certificates
import Decoupling.ProductStates

/-!
# Proposition IV.2 with explicit comparison data

This assembles the actual matrices of (60), (62), (63) and proves both image
equalities (61). The hypotheses are the four comparison equations (48) and
exactness of the original two physical windows. Exactness after adjoining
ancillary blocks is proved in `ProductStates`, not taken as an extra input.

The existence of these comparison data from Assumptions 1–2, and exactness
of the standard Koszul target, remain separate upstream obligations.
-/

namespace Decoupling.PhysicalIsomorphism

open Matrix Stabilization

noncomputable section

variable {F₀ F₁ F₂ G₀ G₁ G₂ : Type*}
  [Fintype F₀] [Fintype F₁] [Fintype F₂]
  [Fintype G₀] [Fintype G₁] [Fintype G₂]
  [DecidableEq F₀] [DecidableEq F₁] [DecidableEq G₀] [DecidableEq G₁]

/-- The input Z-generator matrix in equation (63). -/
def Zhat (d₂ : Matrix F₁ F₂ R) :
    Matrix ((F₁ ⊕ G₀) ⊕ (G₁ ⊕ F₀)) (F₂ ⊕ (G₁ ⊕ F₀)) R :=
  ProductStates.H_Z_dagger d₂

/-- The target Z-generator matrix in equation (63). -/
def Ztilde (td₂ : Matrix G₁ G₂ R) :
    Matrix ((G₁ ⊕ F₀) ⊕ (F₁ ⊕ G₀)) (G₂ ⊕ (F₁ ⊕ G₀)) R :=
  ProductStates.H_Z_dagger td₂

variable (c : ComparisonData R F₀ F₁ G₀ G₁)

/-- The Z-stabilizer image identity, with the original exactness hypotheses. -/
theorem stable_z_image (d₂ : Matrix F₁ F₂ R) (td₂ : Matrix G₁ G₂ R)
    (exactF : ∀ v, c.d₁ *ᵥ v = 0 ↔ ∃ z, d₂ *ᵥ z = v)
    (exactG : ∀ v, c.td₁ *ᵥ v = 0 ↔ ∃ z, td₂ *ᵥ z = v)
    (v : ((G₁ ⊕ F₀) ⊕ (F₁ ⊕ G₀)) → R) :
    (∃ z, c.U *ᵥ (Zhat d₂ *ᵥ z) = v) ↔ Certificates.inImage (Ztilde td₂) v := by
  apply Certificates.z_image_certificate c.H_X_hat c.H_X_tilde (Zhat d₂) (Ztilde td₂)
    c.U c.Uinv c.Ψ₀ c.Ψ₀inv c.U_inverse.1
    (block_mul_reverse c.ρ₀ c.φ₀) c.physical_square
  · exact ProductStates.exactness c.d₁ d₂ exactF
  · exact ProductStates.exactness c.td₁ td₂ exactG

/-- The X-stabilizer image identity uses precisely the inverse dagger. -/
theorem stable_x_image (v : ((G₁ ⊕ F₀) ⊕ (F₁ ⊕ G₀)) → R) :
    (∃ z, dagger c.Uinv *ᵥ (dagger c.H_X_hat *ᵥ z) = v) ↔
      Certificates.inImage (dagger c.H_X_tilde) v :=
  Certificates.x_image_certificate c.H_X_hat c.H_X_tilde
    c.U c.Uinv c.Ψ₀ c.Ψ₀inv c.U_inverse.1
    (block_mul_reverse c.ρ₀ c.φ₀) c.physical_square v

/-- Proposition IV.2: two inverses and both stabilizer-image certificates.
No positive-rank assumptions are made. -/
theorem stable_physical_isomorphism (d₂ : Matrix F₁ F₂ R) (td₂ : Matrix G₁ G₂ R)
    (exactF : ∀ v, c.d₁ *ᵥ v = 0 ↔ ∃ z, d₂ *ᵥ z = v)
    (exactG : ∀ v, c.td₁ *ᵥ v = 0 ↔ ∃ z, td₂ *ᵥ z = v) :
    (c.U * c.Uinv = 1 ∧ c.Uinv * c.U = 1) ∧
    (∀ v, (∃ z, c.U *ᵥ (Zhat d₂ *ᵥ z) = v) ↔ Certificates.inImage (Ztilde td₂) v) ∧
    (∀ v, (∃ z, dagger c.Uinv *ᵥ (dagger c.H_X_hat *ᵥ z) = v) ↔
      Certificates.inImage (dagger c.H_X_tilde) v) :=
  ⟨c.U_inverse, stable_z_image c d₂ td₂ exactF exactG, stable_x_image c⟩

end
end Decoupling.PhysicalIsomorphism
