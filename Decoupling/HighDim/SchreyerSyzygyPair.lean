import Decoupling.HighDim.SchreyerModuleArithmetic

/-! # Normalized module S-polynomials and their actual leading cancellation
Both leading coefficients are inverted in the given field. The formula
works for finite fields, characteristic two, and inhomogeneous vectors.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r : ℕ}

def pairTop (u v : Term D r) : Term D r := (u.1 ⊔ v.1,u.2)

def sPolynomial (f g : Vec K D r) (u v : Term D r) : Vec K D r :=
  (MvPolynomial.monomial ((u.1 ⊔ v.1)-u.1) (coeff f u)⁻¹ : Poly K D) • f -
  (MvPolynomial.monomial ((u.1 ⊔ v.1)-v.1) (coeff g v)⁻¹ : Poly K D) • g

theorem pairTop_left (u v : Term D r) :
    shift ((u.1 ⊔ v.1)-u.1) u=pairTop u v :=
  Prod.ext (tsub_add_cancel_of_le le_sup_left) rfl

theorem pairTop_right (u v : Term D r) (hpos : u.2=v.2) :
    shift ((u.1 ⊔ v.1)-v.1) v=pairTop u v :=
  Prod.ext (tsub_add_cancel_of_le le_sup_right) hpos.symm

/-- The actual S-polynomial lies strictly below the common lcm module term. -/
theorem sPolynomial_below {o : ModuleOrder D r} {f g : Vec K D r} {u v : Term D r}
    (hf : IsLeading o f u) (hg : IsLeading o g v) (hpos : u.2=v.2) :
    StrictlyBelow o (sPolynomial f g u v) (pairTop u v) := by
  have hleft := bounded_monomial_smul hf.2 ((u.1 ⊔ v.1)-u.1) (coeff f u)⁻¹
  have hright := bounded_monomial_smul hg.2 ((u.1 ⊔ v.1)-v.1) (coeff g v)⁻¹
  rw [pairTop_left] at hleft
  rw [pairTop_right u v hpos] at hright
  apply below_sub_of_coeff_eq hleft hright
  rw [← pairTop_left u v,coeff_monomial_smul_shift]
  rw [pairTop_left,← pairTop_right u v hpos,coeff_monomial_smul_shift]
  rw [inv_mul_cancel₀ hf.1,inv_mul_cancel₀ hg.1]

theorem sPolynomial_mem {N : Submodule (Poly K D) (Vec K D r)}
    {f g : Vec K D r} (hf : f∈N) (hg : g∈N) (u v : Term D r) :
    sPolynomial f g u v∈N := N.sub_mem (N.smul_mem _ hf) (N.smul_mem _ hg)

end
end Decoupling.HighDim.SchreyerSyzygy
