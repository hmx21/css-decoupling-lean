import Decoupling.HighDim.PolynomialLaurent

/-!
# HD014 clearing negative exponents in a finite Laurent family

Multiplication by a common genuine Laurent unit produces polynomials in
D variables, with a proved coefficient identity. The original Laurent
module is not replaced by a quotient over twice as many variables.
-/
namespace Decoupling.HighDim.PolynomialLaurent
noncomputable section
variable {K : Type*} [CommRing K] {D : ℕ}
set_option backward.isDefEq.respectTransparency false

def constantExponent (D h : ℕ) : Translation D := fun _ => (h : ℤ)

def shiftedExponent (a : Translation D) (h : ℕ) : Exponent D :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i+h).toNat)

theorem exponentMap_shifted (a : Translation D) (h : ℕ)
    (ha : ∀ i, -(h : ℤ) ≤ a i) :
    exponentMap D (shiftedExponent a h) = constantExponent D h+a := by
  funext i
  change (((a i+h).toNat : ℕ) : ℤ) = (h : ℤ)+a i
  have := ha i
  omega

def clear (f : Laurent K D) (h : ℕ) : Poly D K :=
  f.coeff.sum (fun a c => MvPolynomial.monomial (shiftedExponent a h) c)

theorem clear_correct (f : Laurent K D) (h : ℕ) (hf : LaurentBoxes.Supported f h) :
    inclusion D K (clear f h) = monomial K (constantExponent D h)*f := by
  rw [clear,map_finsuppSum]
  simp only [inclusion_monomial]
  calc
    _ = f.coeff.sum (fun a c => monomial K (constantExponent D h)*AddMonoidAlgebra.single a c) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only
      rw [exponentMap_shifted a h (fun i => ((LaurentBoxes.mem_box a).mp (hf ha) i).1)]
      simp [monomial]
    _ = monomial K (constantExponent D h)*(f.coeff.sum (fun a c => AddMonoidAlgebra.single a c)) := by
      simp only [Finsupp.sum,Finset.mul_sum]
    _ = _ := by rw [AddMonoidAlgebra.sum_coeff_single]

theorem recover_clear (f : Laurent K D) (h : ℕ) (hf : LaurentBoxes.Supported f h) :
    monomial K (-(constantExponent D h))*inclusion D K (clear f h) = f := by
  rw [clear_correct f h hf,← mul_assoc,monomial_neg_mul,one_mul]

def supportRadius (f : Laurent K D) : ℕ :=
  f.coeff.support.sup (fun a => Finset.univ.sup (fun i : Fin D => (a i).natAbs))

theorem supported_radius (f : Laurent K D) : LaurentBoxes.Supported f (supportRadius f) := by
  classical
  intro a ha
  rw [LaurentBoxes.mem_box]
  intro i
  have h₁ : (a i).natAbs ≤ Finset.univ.sup (fun j : Fin D => (a j).natAbs) :=
    Finset.le_sup (f := fun j : Fin D => (a j).natAbs) (Finset.mem_univ i)
  have h₂ : Finset.univ.sup (fun j : Fin D => (a j).natAbs) ≤ supportRadius f :=
    Finset.le_sup (f := fun a : Translation D => Finset.univ.sup (fun j : Fin D => (a j).natAbs)) ha
  have hh : ((a i).natAbs : ℤ) ≤ (supportRadius f : ℤ) := by exact_mod_cast h₁.trans h₂
  have hp : a i ≤ ((a i).natAbs : ℤ) := Int.le_natAbs
  have hm : -(a i) ≤ ((a i).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(a i)))
  omega

theorem finite_family_clear {I : Type*} [Fintype I] (f : I → Laurent K D) :
    ∃ h : ℕ, ∃ g : I → Poly D K,
      ∀ i, inclusion D K (g i) = monomial K (constantExponent D h)*f i := by
  classical
  let h := Finset.univ.sup (fun i => supportRadius (f i))
  refine ⟨h,fun i => clear (f i) h,fun i => clear_correct (f i) h ?_⟩
  intro a ha
  rw [LaurentBoxes.mem_box]
  have hb := (LaurentBoxes.mem_box a).mp (supported_radius (f i) ha)
  have hh : supportRadius (f i) ≤ h :=
    Finset.le_sup (f := fun i => supportRadius (f i)) (Finset.mem_univ i)
  intro j
  have := hb j
  omega

end
end Decoupling.HighDim.PolynomialLaurent
