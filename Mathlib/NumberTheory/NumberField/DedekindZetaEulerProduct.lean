/-
Copyright (c) 2026 Bob McElrath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bob McElrath
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Coefficients for the Dedekind zeta function

This file packages the coefficients of `NumberField.dedekindZeta` as an arithmetic function.
The eventual goal is to prove multiplicativity and derive an Euler product.
-/

@[expose] public section

noncomputable section

open Filter
open scoped LSeries.notation

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The fiber of the absolute norm map over `n`. -/
def NormFiber (n : ℕ) := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- The arithmetic function counting integral ideals of a given absolute norm. -/
noncomputable def idealNormCount : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  map_zero' := rfl

@[simp]
theorem idealNormCount_zero : idealNormCount K 0 = 0 :=
  rfl

theorem idealNormCount_apply_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    idealNormCount K n = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
  simp [idealNormCount, hn]

theorem isCoprime_of_coprime_absNorm {I J : Ideal (𝓞 K)}
    (hIJ : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J)) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) hsup
  have hMI : I ≤ M := le_trans le_sup_left hle
  have hMJ : J ≤ M := le_trans le_sup_right hle
  have hdvd : Ideal.absNorm M ∣ Nat.gcd (Ideal.absNorm I) (Ideal.absNorm J) :=
    Nat.dvd_gcd (Ideal.absNorm_dvd_absNorm_of_le hMI) (Ideal.absNorm_dvd_absNorm_of_le hMJ)
  have hnormM : Ideal.absNorm M = 1 := by
    rw [hIJ.gcd_eq_one] at hdvd
    exact Nat.eq_one_of_dvd_one hdvd
  exact hM.ne_top ((Ideal.absNorm_eq_one_iff).mp hnormM)

/-- The rational prime lying under a height-one prime of `𝓞 K`. -/
noncomputable def ratPrime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.absNorm (Ideal.under ℤ v.asIdeal)

omit [NumberField K] in
theorem ratPrime_prime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (ratPrime K v).Prime := by
  letI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  simpa [ratPrime] using Nat.absNorm_under_prime v.asIdeal

theorem absNorm_maxPowDividing_dvd (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Ideal.absNorm (v.maxPowDividing I) ∣ Ideal.absNorm I := by
  have hdiv : v.maxPowDividing I ∣
      ∏ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), w.maxPowDividing I :=
    finprod_mem_dvd v (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at hdiv
  exact map_dvd Ideal.absNorm hdiv

/-- The `m`-part of an ideal, split according to the rational prime below each height-one prime. -/
noncomputable def splitIdealLeft (I : Ideal (𝓞 K)) (m : ℕ) : Ideal (𝓞 K) :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    if ratPrime K v ∣ m then v.maxPowDividing I else 1

/-- The `n`-part of an ideal, split according to the rational prime below each height-one prime. -/
noncomputable def splitIdealRight (I : Ideal (𝓞 K)) (n : ℕ) : Ideal (𝓞 K) :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    if ratPrime K v ∣ n then v.maxPowDividing I else 1

theorem absNorm_maxPowDividing_is_prime_pow (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ e : ℕ, Ideal.absNorm (v.maxPowDividing I) = ratPrime K v ^ e := by
  classical
  letI : v.asIdeal.LiesOver (Ideal.span {(ratPrime K v : ℤ)}) := Int.liesOver_span_absNorm v.asIdeal
  refine ⟨(Ideal.span {(ratPrime K v : ℤ)}).inertiaDeg v.asIdeal *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
  rw [v.maxPowDividing_eq_pow_multiset_count (I := I) hI, map_pow,
    Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal (ratPrime_prime K v), pow_mul]

theorem splitIdeal_mul {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    splitIdealLeft K I m * splitIdealRight K I n = I := by
  classical
  let f : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Ideal (𝓞 K) := fun v ↦ v.maxPowDividing I
  let s : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := {v | ratPrime K v ∣ m}
  let t : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := {v | ratPrime K v ∣ n}
  have hf : Function.HasFiniteMulSupport f := Ideal.hasFiniteMulSupport hI
  have hf_left : Function.HasFiniteMulSupport (s.mulIndicator f) := by
    refine hf.subset ?_
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right
  have hf_right : Function.HasFiniteMulSupport (sᶜ.mulIndicator f) := by
    refine hf.subset ?_
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right
  have hleft :
      splitIdealLeft K I m = ∏ᶠ v ∈ s, f v := by
    rw [splitIdealLeft, finprod_mem_def]
    apply finprod_congr
    intro v
    simp [f, s, Set.mulIndicator_apply]
  have hright :
      splitIdealRight K I n = ∏ᶠ v ∈ t, f v := by
    rw [splitIdealRight, finprod_mem_def]
    apply finprod_congr
    intro v
    simp [f, t, Set.mulIndicator_apply]
  have hts :
      ∏ᶠ v ∈ t, f v = ∏ᶠ v ∈ sᶜ, f v := by
    apply finprod_mem_inter_mulSupport_eq' (f := f) (s := t) (t := sᶜ)
    intro v hv
    constructor
    · intro hvn
      simp [s]
      intro hvm
      have hcop : Nat.Coprime (ratPrime K v) n := Nat.Coprime.of_dvd_left hvm hmn
      exact ((ratPrime_prime K v).coprime_iff_not_dvd.mp hcop) hvn
    · intro hvm
      have hcount_pos :
          0 < Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
        have hv' : f v ≠ 1 := by
          simpa [Function.mem_mulSupport] using hv
        by_contra hcount
        apply hv'
        rw [show f v =
            v.asIdeal ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) by
          simpa [f] using v.maxPowDividing_eq_pow_multiset_count (I := I) hI,
          Nat.eq_zero_of_not_pos hcount]
        simp
      have hle : v.maxPowDividing I ≤ v.asIdeal := by
        rw [v.maxPowDividing_eq_pow_multiset_count (I := I) hI]
        simpa using
          (Ideal.pow_le_pow_right hcount_pos :
            v.asIdeal ^
                Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) ≤
              v.asIdeal ^ 1)
      have hpdvdnorm : ratPrime K v ∣ Ideal.absNorm (f v) := by
        exact dvd_trans
          (by simpa [ratPrime] using Int.absNorm_under_dvd_absNorm (I := v.asIdeal))
          (Ideal.absNorm_dvd_absNorm_of_le hle)
      have hpdvdmn : ratPrime K v ∣ m * n := dvd_trans hpdvdnorm (hNorm ▸ absNorm_maxPowDividing_dvd K v hI)
      rcases (ratPrime_prime K v).dvd_mul.mp hpdvdmn with hpm | hpn
      · exact False.elim (hvm hpm)
      · exact hpn
  calc
    splitIdealLeft K I m * splitIdealRight K I n
        = (∏ᶠ v ∈ s, f v) * (∏ᶠ v ∈ sᶜ, f v) := by rw [hleft, hright, hts]
    _ = (∏ᶠ v, s.mulIndicator f v) * (∏ᶠ v, sᶜ.mulIndicator f v) := by
      rw [← finprod_mem_def, ← finprod_mem_def]
    _ = ∏ᶠ v, s.mulIndicator f v * sᶜ.mulIndicator f v := by
      rw [← finprod_mul_distrib hf_left hf_right]
    _ = ∏ᶠ v, f v := by
      apply finprod_congr
      intro v
      simpa [Set.mulIndicator_apply] using
        congrFun (Set.mulIndicator_mul_compl_eq_piecewise (s := s) (f := f) (g := f)) v
    _ = I := Ideal.finprod_heightOneSpectrum_factorization hI

theorem splitIdealLeft_absNorm_coprime_right {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥)
    (hmn : Nat.Coprime m n) :
    Nat.Coprime (Ideal.absNorm (splitIdealLeft K I m)) n := by
  rw [splitIdealLeft]
  have habs :
      Ideal.absNorm (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          if ratPrime K v ∣ m then v.maxPowDividing I else 1) =
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (if ratPrime K v ∣ m then v.maxPowDividing I else 1) := by
    simpa using
      (Ideal.absNorm.toMonoidHom.map_finprod_of_preimage_one
        (fun J hJ => by simpa using (Ideal.absNorm_eq_one_iff.mp hJ))
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          if ratPrime K v ∣ m then v.maxPowDividing I else 1))
  rw [habs]
  refine finprod_induction
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Ideal.absNorm (if ratPrime K v ∣ m then v.maxPowDividing I else 1))
    (p := fun a : ℕ => Nat.Coprime a n)
    (by simp)
    (fun a b ha hb => ha.mul_left hb)
    ?_
  intro v
  by_cases hv : ratPrime K v ∣ m
  · have hcop : Nat.Coprime (ratPrime K v) n := Nat.Coprime.of_dvd_left hv hmn
    obtain ⟨e, he⟩ := absNorm_maxPowDividing_is_prime_pow K v hI
    simpa [hv, he] using hcop.pow_left e
  · simp [hv]

theorem splitIdealRight_absNorm_coprime_left {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥)
    (hmn : Nat.Coprime m n) :
    Nat.Coprime m (Ideal.absNorm (splitIdealRight K I n)) := by
  rw [splitIdealRight]
  have habs :
      Ideal.absNorm (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          if ratPrime K v ∣ n then v.maxPowDividing I else 1) =
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Ideal.absNorm (if ratPrime K v ∣ n then v.maxPowDividing I else 1) := by
    simpa using
      (Ideal.absNorm.toMonoidHom.map_finprod_of_preimage_one
        (fun J hJ => by simpa using (Ideal.absNorm_eq_one_iff.mp hJ))
        (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          if ratPrime K v ∣ n then v.maxPowDividing I else 1))
  rw [habs]
  refine finprod_induction
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Ideal.absNorm (if ratPrime K v ∣ n then v.maxPowDividing I else 1))
    (p := fun a : ℕ => Nat.Coprime m a)
    (by simp)
    (fun a b ha hb => ha.mul_right hb)
    ?_
  intro v
  by_cases hv : ratPrime K v ∣ n
  · have hcop : Nat.Coprime m (ratPrime K v) := Nat.Coprime.of_dvd_right hv hmn
    obtain ⟨e, he⟩ := absNorm_maxPowDividing_is_prime_pow K v hI
    simpa [hv, he] using hcop.pow_right e
  · simp [hv]

theorem splitIdealLeft_absNorm_eq {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    Ideal.absNorm (splitIdealLeft K I m) = m := by
  let a := Ideal.absNorm (splitIdealLeft K I m)
  let b := Ideal.absNorm (splitIdealRight K I n)
  have hab : a * b = m * n := by
    dsimp [a, b]
    simpa [map_mul, hNorm] using congrArg Ideal.absNorm (splitIdeal_mul K hI hmn hNorm)
  have ha_coprime : Nat.Coprime a n := by
    simpa [a] using splitIdealLeft_absNorm_coprime_right K hI hmn
  have hm_dvd_a : m ∣ a := by
    have hm_dvd_ab : m ∣ a * b := by
      rw [hab]
      exact dvd_mul_right m n
    have hb_coprime : Nat.Coprime m b := by
      simpa [b] using splitIdealRight_absNorm_coprime_left K hI hmn
    exact hb_coprime.dvd_of_dvd_mul_right hm_dvd_ab
  have ha_dvd_m : a ∣ m := by
    have ha_dvd_mn : a ∣ m * n := by
      exact Dvd.intro b hab
    exact ha_coprime.dvd_of_dvd_mul_right ha_dvd_mn
  exact Nat.dvd_antisymm ha_dvd_m hm_dvd_a

theorem splitIdealRight_absNorm_eq {I : Ideal (𝓞 K)} {m n : ℕ} (hI : I ≠ ⊥) (hmn : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    Ideal.absNorm (splitIdealRight K I n) = n := by
  let a := Ideal.absNorm (splitIdealLeft K I m)
  let b := Ideal.absNorm (splitIdealRight K I n)
  have hab : a * b = m * n := by
    dsimp [a, b]
    simpa [map_mul, hNorm] using congrArg Ideal.absNorm (splitIdeal_mul K hI hmn hNorm)
  have hb_coprime : Nat.Coprime m b := by
    simpa [b] using splitIdealRight_absNorm_coprime_left K hI hmn
  have hn_dvd_b : n ∣ b := by
    have hn_dvd_ab : n ∣ a * b := by
      rw [hab]
      exact dvd_mul_left n m
    have ha_coprime : Nat.Coprime a n := by
      simpa [a] using splitIdealLeft_absNorm_coprime_right K hI hmn
    exact ha_coprime.symm.dvd_of_dvd_mul_left hn_dvd_ab
  have hb_dvd_n : b ∣ n := by
    have hb_dvd_mn : b ∣ m * n := by
      exact Dvd.intro a (by simpa [Nat.mul_comm] using hab)
    exact hb_coprime.symm.dvd_of_dvd_mul_left hb_dvd_mn
  exact Nat.dvd_antisymm hb_dvd_n hn_dvd_b

/-- Multiplication of ideals induces a map on fibers of the absolute norm. -/
def mulOnAbsNormFiber (m n : ℕ) :
    NormFiber K m → NormFiber K n → NormFiber K (m * n) :=
  fun ⟨I, hI⟩ ⟨J, hJ⟩ => ⟨I * J, by
    rw [map_mul, hI, hJ]⟩

@[simp]
theorem mulOnAbsNormFiber_fst (m n : ℕ)
    (I : NormFiber K m) (J : NormFiber K n) :
    (mulOnAbsNormFiber K m n I J).1 = I.1 * J.1 :=
  rfl

def mulOnAbsNormFiberProd (m n : ℕ) :
    NormFiber K m × NormFiber K n → NormFiber K (m * n) :=
  fun IJ => mulOnAbsNormFiber K m n IJ.1 IJ.2

def splitNormFiber {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    NormFiber K (m * n) → NormFiber K m × NormFiber K n :=
  fun I =>
    let J := I.1
    let hJ : J ≠ ⊥ := by
      intro hbot
      have hmn0 : m * n = 0 := by
        have hnorm : Ideal.absNorm J = m * n := I.2
        simpa [J, hbot] using hnorm.symm
      rcases Nat.mul_eq_zero.mp hmn0 with h0 | h0
      · exact False.elim (hm h0)
      · exact False.elim (hn h0)
    (⟨splitIdealLeft K J m, splitIdealLeft_absNorm_eq K hJ h I.2⟩,
      ⟨splitIdealRight K J n, splitIdealRight_absNorm_eq K hJ h I.2⟩)

theorem splitNormFiber_leftInverse {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Function.LeftInverse (splitNormFiber K hm hn h) (mulOnAbsNormFiberProd K m n) := by
  intro IJ
  rcases IJ with ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    change splitIdealLeft K (I * J) m = I
    have hI0 : I ≠ ⊥ := by
      intro hbot
      exact hm (by simpa [hbot] using hI.symm)
    have hJ0 : J ≠ ⊥ := by
      intro hbot
      exact hn (by simpa [hbot] using hJ.symm)
    have hIJ : I * J ≠ ⊥ := by
      exact mul_ne_zero hI0 hJ0
    have hmul : Ideal.absNorm (I * J) = m * n := by simp [map_mul, hI, hJ]
    have hsplit_mul := splitIdeal_mul K hIJ h hmul
    have hcop_leftJ : Nat.Coprime (Ideal.absNorm (splitIdealLeft K (I * J) m)) (Ideal.absNorm J) := by
      simpa [hJ] using splitIdealLeft_absNorm_coprime_right K hIJ h
    have hcopIdeals_leftJ : IsCoprime (splitIdealLeft K (I * J) m) J :=
      isCoprime_of_coprime_absNorm K hcop_leftJ
    have hleft_dvd_prod : splitIdealLeft K (I * J) m ∣ I * J := by
      refine ⟨splitIdealRight K (I * J) n, hsplit_mul.symm⟩
    have hleft_dvd_I : splitIdealLeft K (I * J) m ∣ I :=
      hcopIdeals_leftJ.dvd_of_dvd_mul_right hleft_dvd_prod
    have hcop_Iright : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm (splitIdealRight K (I * J) n)) := by
      simpa [hI] using splitIdealRight_absNorm_coprime_left K hIJ h
    have hcopIdeals_Iright : IsCoprime I (splitIdealRight K (I * J) n) :=
      isCoprime_of_coprime_absNorm K hcop_Iright
    have hI_dvd_prod : I ∣ I * J := ⟨J, rfl⟩
    have hI_dvd_left : I ∣ splitIdealLeft K (I * J) m := by
      rw [← hsplit_mul] at hI_dvd_prod
      exact hcopIdeals_Iright.dvd_of_dvd_mul_right hI_dvd_prod
    exact le_antisymm (Ideal.dvd_iff_le.mp hI_dvd_left) (Ideal.dvd_iff_le.mp hleft_dvd_I)
  · apply Subtype.ext
    change splitIdealRight K (I * J) n = J
    have hI0 : I ≠ ⊥ := by
      intro hbot
      exact hm (by simpa [hbot] using hI.symm)
    have hJ0 : J ≠ ⊥ := by
      intro hbot
      exact hn (by simpa [hbot] using hJ.symm)
    have hIJ : I * J ≠ ⊥ := by
      exact mul_ne_zero hI0 hJ0
    have hmul : Ideal.absNorm (I * J) = m * n := by simp [map_mul, hI, hJ]
    have hsplit_mul := splitIdeal_mul K hIJ h hmul
    have hcop_Iright : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm (splitIdealRight K (I * J) n)) := by
      simpa [hI] using splitIdealRight_absNorm_coprime_left K hIJ h
    have hcopIdeals_Iright : IsCoprime I (splitIdealRight K (I * J) n) :=
      isCoprime_of_coprime_absNorm K hcop_Iright
    have hright_dvd_prod : splitIdealRight K (I * J) n ∣ I * J := by
      rw [mul_comm] at hsplit_mul
      refine ⟨splitIdealLeft K (I * J) m, hsplit_mul.symm⟩
    have hright_dvd_J : splitIdealRight K (I * J) n ∣ J :=
      hcopIdeals_Iright.symm.dvd_of_dvd_mul_left hright_dvd_prod
    have hcop_leftJ : Nat.Coprime (Ideal.absNorm (splitIdealLeft K (I * J) m)) (Ideal.absNorm J) := by
      simpa [hJ] using splitIdealLeft_absNorm_coprime_right K hIJ h
    have hcopIdeals_leftJ : IsCoprime (splitIdealLeft K (I * J) m) J :=
      isCoprime_of_coprime_absNorm K hcop_leftJ
    have hJ_dvd_prod : J ∣ I * J := ⟨I, by ac_rfl⟩
    have hJ_dvd_right : J ∣ splitIdealRight K (I * J) n := by
      rw [← hsplit_mul] at hJ_dvd_prod
      exact hcopIdeals_leftJ.symm.dvd_of_dvd_mul_left hJ_dvd_prod
    exact le_antisymm (Ideal.dvd_iff_le.mp hJ_dvd_right) (Ideal.dvd_iff_le.mp hright_dvd_J)

theorem splitNormFiber_rightInverse {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Function.RightInverse (splitNormFiber K hm hn h) (mulOnAbsNormFiberProd K m n) := by
  intro I
  apply Subtype.ext
  simp [splitNormFiber, mulOnAbsNormFiberProd, mulOnAbsNormFiber]
  let J := I.1
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hmn0 : m * n = 0 := by
      have hnorm : Ideal.absNorm J = m * n := I.2
      simpa [J, hbot] using hnorm.symm
    rcases Nat.mul_eq_zero.mp hmn0 with h0 | h0
    · exact False.elim (hm h0)
    · exact False.elim (hn h0)
  exact splitIdeal_mul K hJ h I.2

noncomputable def normFiberEquivProd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    NormFiber K (m * n) ≃ NormFiber K m × NormFiber K n where
  toFun := splitNormFiber K hm hn h
  invFun := mulOnAbsNormFiberProd K m n
  left_inv := splitNormFiber_rightInverse K hm hn h
  right_inv := splitNormFiber_leftInverse K hm hn h

theorem idealNormCount_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    idealNormCount K (m * n) = idealNormCount K m * idealNormCount K n := by
  by_cases hm : m = 0
  · subst hm
    simp
  by_cases hn : n = 0
  · subst hn
    simp
  rw [idealNormCount_apply_of_ne_zero K (Nat.mul_ne_zero hm hn),
    idealNormCount_apply_of_ne_zero K hm, idealNormCount_apply_of_ne_zero K hn,
    ← Nat.card_prod]
  exact Nat.card_congr (normFiberEquivProd K hm hn h)

theorem idealNormCount_isMultiplicative : (idealNormCount K).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · rw [idealNormCount_apply_of_ne_zero K one_ne_zero]
    simp [Ideal.absNorm_eq_one_iff]
  · intro m n h
    exact idealNormCount_mul_of_coprime K h

noncomputable def dedekindZetaSummand (s : ℂ) : ArithmeticFunction ℂ where
  toFun n := LSeries.term (fun n ↦ (idealNormCount K n : ℂ)) s n
  map_zero' := LSeries.term_zero _ _

theorem dedekindZetaSummand_apply (s : ℂ) (n : ℕ) :
    dedekindZetaSummand K s n = LSeries.term (fun n ↦ (idealNormCount K n : ℂ)) s n :=
  rfl

theorem dedekindZetaSummand_isMultiplicative (s : ℂ) :
    (dedekindZetaSummand K s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [dedekindZetaSummand, LSeries.term_def₀, idealNormCount_isMultiplicative]
  · intro m n hm hn hmn
    have hpow : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
      simpa only [Nat.cast_mul, Complex.ofReal_natCast]
        using Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)
    rw [dedekindZetaSummand_apply, dedekindZetaSummand_apply, dedekindZetaSummand_apply,
      LSeries.term_def₀ (by simp),
      LSeries.term_def₀ (by simp),
      LSeries.term_def₀ (by simp),
      (idealNormCount_isMultiplicative K).2 hmn, hpow]
    simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

theorem summable_dedekindZetaSummand (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dedekindZetaSummand K s n‖) := by
  have hO :
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) =O[atTop]
        fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    have hlim :
        Tendsto (fun n : ℕ =>
          (∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) / ((n : ℝ) ^ (1 : ℝ))) atTop
          (nhds ((2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^
            InfinitePlace.nrComplexPlaces K * Units.regulator K * classNumber K) /
            (Units.torsionOrder K * Real.sqrt |discr K|) : ℝ)) := by
      simpa [Real.rpow_one] using
        (((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ by
          simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
          congr
          conv_rhs =>
            rw [Finset.sum_congr rfl fun k hk ↦ idealNormCount_apply_of_ne_zero K
              (Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1)]
          rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
            show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
            show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
              have hfinite : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} := by
                exact Ideal.finite_setOf_absNorm_eq 0
              letI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = 0}
              rw [Nat.card_eq_fintype_card]
              simp [Ideal.absNorm_eq_zero_iff],
            Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
            ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
          simp [Set.coe_eq_subtype])
    exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (a := ((2 ^
      InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
      Units.regulator K * classNumber K) / (Units.torsionOrder K * Real.sqrt |discr K|) : ℝ)) hlim
  have hS :
      LSeriesSummable (fun n ↦ (idealNormCount K n : ℝ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _)
      (show (0 : ℝ) ≤ 1 by norm_num) hs
  rw [LSeriesSummable, ← summable_norm_iff] at hS
  simpa [dedekindZetaSummand_apply] using hS

theorem tsum_dedekindZetaSummand (s : ℂ) :
    ∑' n : ℕ, dedekindZetaSummand K s n = dedekindZeta K s := by
  rw [NumberField.dedekindZeta, LSeries]
  refine tsum_congr fun n ↦ ?_
  by_cases hn : n = 0
  · simp [dedekindZetaSummand, hn]
  · simp [dedekindZetaSummand, LSeries.term_def, idealNormCount_apply_of_ne_zero K hn, hn]

theorem dedekindZeta_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, ∑' e : ℕ, dedekindZetaSummand K s (p ^ e))
      atTop (nhds (dedekindZeta K s)) := by
  rw [← tsum_dedekindZetaSummand K s]
  exact ArithmeticFunction.IsMultiplicative.eulerProduct
    (dedekindZetaSummand_isMultiplicative K s) (summable_dedekindZetaSummand K s hs)

theorem dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s := by
  refine LSeries_congr (s := s) ?_
  intro n hn
  rw [idealNormCount_apply_of_ne_zero K hn]

/-! ### Bridge helpers for split-prime ideal counts and PID element counts

These two helpers provide a uniform interface for closing bridge lemmas in
applications such as `EisensteinIntegerHecke` and `HeckeZetaFE_FromTheta`.

The proofs below are tagged as named leaf `sorry`s for Phase 3a follow-up.
The statements are stable; downstream files may use them immediately.
-/

/-- **Split prime power count.**

If a rational prime `p` is split in `𝓞 K` as `p · 𝓞_K = 𝔭₁ · 𝔭₂` with two
distinct primes of absolute norm `p`, then the integral ideals of norm `p^k`
are exactly `{𝔭₁^a · 𝔭₂^(k-a) : a ∈ Fin (k+1)}`, hence
`idealNormCount K (p^k) = k + 1`.

Sub-leaf `exists_split_factorization_of_absNorm_pow` (below): every ideal of
norm `p^k` factors as `𝔭₁^a · 𝔭₂^(k-a)` for some `a ≤ k`. Estimated 80–120 LOC,
deferred to follow-up Phase 3a. -/
theorem exists_split_factorization_of_absNorm_pow {p : ℕ} (hp : p.Prime)
    (𝔭₁ 𝔭₂ : Ideal (𝓞 K))
    (h𝔭₁ : 𝔭₁.IsPrime) (h𝔭₂ : 𝔭₂.IsPrime) (hne : 𝔭₁ ≠ 𝔭₂)
    (hN₁ : Ideal.absNorm 𝔭₁ = p) (hN₂ : Ideal.absNorm 𝔭₂ = p)
    (hsplit : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) = 𝔭₁ * 𝔭₂)
    {k : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    ∃ a ≤ k, I = 𝔭₁ ^ a * 𝔭₂ ^ (k - a) := by
  classical
  -- Setup: 𝔭ᵢ are nonzero primes (so prime in the UFM `Ideal (𝓞 K)`).
  have h𝔭₁_ne : 𝔭₁ ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hN₁; exact hp.ne_zero hN₁.symm
  have h𝔭₂_ne : 𝔭₂ ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hN₂; exact hp.ne_zero hN₂.symm
  have h𝔭₁_prime : Prime 𝔭₁ := Ideal.prime_of_isPrime h𝔭₁_ne h𝔭₁
  have h𝔭₂_prime : Prime 𝔭₂ := Ideal.prime_of_isPrime h𝔭₂_ne h𝔭₂
  have h12 : ¬ Associated 𝔭₁ 𝔭₂ := fun h => hne (by
    simpa using normalize_eq_normalize_iff_associated.mpr h)
  -- I is nonzero: absNorm I = p^k ≠ 0.
  have hI_ne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hI
    exact (pow_ne_zero k hp.ne_zero) hI.symm
  -- Step 1: I divides ⟨p⟩ ^ k = (𝔭₁ * 𝔭₂) ^ k.
  -- Because (absNorm I : 𝓞 K) ∈ I, so the principal ideal ⟨p^k⟩ ≤ I, i.e. I ∣ ⟨p^k⟩.
  have hpk_mem : ((p : 𝓞 K) ^ k) ∈ I := by
    have := Ideal.absNorm_mem I
    rw [hI] at this
    exact_mod_cast this
  have hI_dvd_pk : I ∣ Ideal.span ({(p : 𝓞 K) ^ k} : Set (𝓞 K)) := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hpk_mem
  -- Rewrite ⟨p^k⟩ = ⟨p⟩^k = (𝔭₁ * 𝔭₂)^k.
  have hspan_pow : Ideal.span ({(p : 𝓞 K) ^ k} : Set (𝓞 K)) = (𝔭₁ * 𝔭₂) ^ k := by
    rw [← hsplit, Ideal.span_singleton_pow]
  rw [hspan_pow, mul_pow] at hI_dvd_pk
  -- Step 2: pass to normalized factors.
  have hpk_ne : (𝔭₁ ^ k * 𝔭₂ ^ k : Ideal (𝓞 K)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ h𝔭₁_ne) (pow_ne_zero _ h𝔭₂_ne)
  have hfac_le :
      UniqueFactorizationMonoid.normalizedFactors I ≤
        UniqueFactorizationMonoid.normalizedFactors (𝔭₁ ^ k * 𝔭₂ ^ k) :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI_ne hpk_ne).mp
      hI_dvd_pk
  -- Compute normalizedFactors of the RHS: k • {𝔭₁} + k • {𝔭₂}.
  have hRHS :
      UniqueFactorizationMonoid.normalizedFactors (𝔭₁ ^ k * 𝔭₂ ^ k) =
        k • ({𝔭₁} : Multiset (Ideal (𝓞 K))) + k • ({𝔭₂} : Multiset (Ideal (𝓞 K))) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ h𝔭₁_ne)
          (pow_ne_zero _ h𝔭₂_ne),
        UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_pow,
        UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭₁_prime.irreducible,
        UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭₂_prime.irreducible,
        normalize_eq, normalize_eq]
  -- Define a = count 𝔭₁, b = count 𝔭₂.
  set a := Multiset.count 𝔭₁ (UniqueFactorizationMonoid.normalizedFactors I) with ha_def
  set b := Multiset.count 𝔭₂ (UniqueFactorizationMonoid.normalizedFactors I) with hb_def
  -- Bounds a ≤ k, b ≤ k from hfac_le and Multiset.le_iff_count.
  have ha_le : a ≤ k := by
    have h1 := Multiset.le_iff_count.mp hfac_le 𝔭₁
    rw [hRHS, Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
      Multiset.count_singleton_self, Multiset.count_singleton, if_neg hne,
      mul_one, mul_zero, Nat.add_zero] at h1
    exact h1
  have hb_le : b ≤ k := by
    have h1 := Multiset.le_iff_count.mp hfac_le 𝔭₂
    rw [hRHS, Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
      Multiset.count_singleton, Multiset.count_singleton_self, if_neg hne.symm,
      mul_one, mul_zero, Nat.zero_add] at h1
    exact h1
  -- Every element of normalizedFactors I is associated to 𝔭₁ or 𝔭₂ (since it's a factor of RHS).
  have hfac_eq :
      UniqueFactorizationMonoid.normalizedFactors I =
        a • ({𝔭₁} : Multiset (Ideal (𝓞 K))) + b • ({𝔭₂} : Multiset (Ideal (𝓞 K))) := by
    refine Multiset.ext.mpr fun q => ?_
    by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors I
    · -- q is in normalizedFactors I, hence in RHS multiset, hence q = 𝔭₁ or q = 𝔭₂.
      have hq_in : q ∈ k • ({𝔭₁} : Multiset (Ideal (𝓞 K))) +
                       k • ({𝔭₂} : Multiset (Ideal (𝓞 K))) := by
        rw [← hRHS]; exact Multiset.mem_of_le hfac_le hq
      simp only [Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton] at hq_in
      rcases hq_in with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
      · rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
          Multiset.count_singleton_self, Multiset.count_singleton, if_neg hne,
          mul_one, mul_zero, Nat.add_zero]
      · rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
          Multiset.count_singleton, Multiset.count_singleton_self, if_neg hne.symm,
          mul_one, mul_zero, Nat.zero_add]
    · -- q ∉ normalizedFactors I: count is 0 on LHS.
      rw [Multiset.count_eq_zero.mpr hq, Multiset.count_add, Multiset.count_nsmul,
        Multiset.count_nsmul]
      by_cases hq1 : q = 𝔭₁
      · subst hq1
        have ha0 : a = 0 := by rw [ha_def]; exact Multiset.count_eq_zero.mpr hq
        rw [ha0, Nat.zero_mul, Nat.zero_add,
          Multiset.count_singleton, if_neg hne, mul_zero]
      · by_cases hq2 : q = 𝔭₂
        · subst hq2
          have hb0 : b = 0 := by rw [hb_def]; exact Multiset.count_eq_zero.mpr hq
          rw [hb0, Nat.zero_mul, Nat.add_zero,
            Multiset.count_singleton, if_neg hne.symm, mul_zero]
        · rw [Multiset.count_singleton, if_neg hq1, mul_zero,
            Multiset.count_singleton, if_neg hq2, mul_zero, Nat.add_zero]
  -- Step 3: I = 𝔭₁ ^ a * 𝔭₂ ^ b (via prod_normalizedFactors and that I is normalized).
  have hI_eq : I = 𝔭₁ ^ a * 𝔭₂ ^ b := by
    have hprod : (UniqueFactorizationMonoid.normalizedFactors I).prod = I := by
      rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hI_ne, normalize_eq]
    rw [← hprod, hfac_eq]
    rw [Multiset.prod_add, Multiset.prod_nsmul, Multiset.prod_nsmul,
      Multiset.prod_singleton, Multiset.prod_singleton]
  -- Step 4: norm constraint forces a + b = k.
  have hab : a + b = k := by
    have hnorm : Ideal.absNorm (𝔭₁ ^ a * 𝔭₂ ^ b) = p ^ k := by rw [← hI_eq]; exact hI
    rw [map_mul, map_pow, map_pow, hN₁, hN₂, ← pow_add] at hnorm
    exact Nat.pow_right_injective hp.two_le hnorm
  refine ⟨a, ?_, ?_⟩
  · omega
  · rw [hI_eq]; congr 1; congr 1; omega

/-- See sub-leaf above. -/
theorem idealNormCount_split_pow {p : ℕ} (hp : p.Prime)
    (𝔭₁ 𝔭₂ : Ideal (𝓞 K))
    (h𝔭₁ : 𝔭₁.IsPrime) (h𝔭₂ : 𝔭₂.IsPrime) (hne : 𝔭₁ ≠ 𝔭₂)
    (hN₁ : Ideal.absNorm 𝔭₁ = p) (hN₂ : Ideal.absNorm 𝔭₂ = p)
    (hsplit : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) = 𝔭₁ * 𝔭₂)
    (k : ℕ) :
    idealNormCount K (p ^ k) = k + 1 := by
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [idealNormCount_apply_of_ne_zero K hpk_ne]
  -- Bijection: Fin (k+1) ≃ {I // absNorm I = p^k} via a ↦ 𝔭₁^a · 𝔭₂^(k-a).
  have h𝔭₁_ne : 𝔭₁ ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hN₁; exact hp.ne_zero hN₁.symm
  have h𝔭₂_ne : 𝔭₂ ≠ ⊥ := fun h => by
    rw [h, Ideal.absNorm_bot] at hN₂; exact hp.ne_zero hN₂.symm
  have h𝔭₁_prime : Prime 𝔭₁ := Ideal.prime_of_isPrime h𝔭₁_ne h𝔭₁
  have h𝔭₂_prime : Prime 𝔭₂ := Ideal.prime_of_isPrime h𝔭₂_ne h𝔭₂
  classical
  let f : Fin (k + 1) → {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} :=
    fun a => ⟨𝔭₁ ^ a.1 * 𝔭₂ ^ (k - a.1), by
      rw [map_mul, map_pow, map_pow, hN₁, hN₂, ← pow_add,
        Nat.add_sub_cancel' (Nat.lt_succ_iff.mp a.2)]⟩
  rw [show (k + 1 : ℕ) = Nat.card (Fin (k + 1)) by simp]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · -- Injectivity: 𝔭₁^a · 𝔭₂^(k-a) = 𝔭₁^b · 𝔭₂^(k-b) → a = b.
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hfab
    have heq : 𝔭₁ ^ a * 𝔭₂ ^ (k - a) = 𝔭₁ ^ b * 𝔭₂ ^ (k - b) := by
      simpa [f] using congrArg Subtype.val hfab
    -- Take multiplicity at 𝔭₁ on both sides via UFM.
    have ha_le : a ≤ k := Nat.lt_succ_iff.mp ha
    have hb_le : b ≤ k := Nat.lt_succ_iff.mp hb
    apply Fin.ext
    change a = b
    have hcount := congrArg
      (Multiset.count 𝔭₁ ∘ UniqueFactorizationMonoid.normalizedFactors) heq
    have h12 : ¬ Associated 𝔭₁ 𝔭₂ := fun h => hne (by
      simpa using normalize_eq_normalize_iff_associated.mpr h)
    simp only [Function.comp_apply,
      UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ h𝔭₁_ne)
        (pow_ne_zero _ h𝔭₂_ne),
      UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_add, Multiset.count_nsmul,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭₁_prime.irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭₂_prime.irreducible,
      normalize_eq, Multiset.count_singleton_self,
      Multiset.count_singleton, if_neg hne, if_neg (Ne.symm hne)] at hcount
    -- hcount should be: a * 1 + (k - a) * 0 = b * 1 + (k - b) * 0
    simpa using hcount
  · -- Surjectivity: delegated to sub-leaf.
    rintro ⟨I, hI⟩
    obtain ⟨a, ha_le, hIeq⟩ :=
      exists_split_factorization_of_absNorm_pow K hp 𝔭₁ 𝔭₂ h𝔭₁ h𝔭₂ hne hN₁ hN₂ hsplit hI
    exact ⟨⟨a, Nat.lt_succ_of_le ha_le⟩, by simp [f, hIeq]⟩

/-- **Split prime power successor identity.**

Specialization of `idealNormCount_split_pow`: for split `p`, the count
increments by 1 per prime power level. -/
theorem idealNormCount_split_succ {p : ℕ} (hp : p.Prime)
    (𝔭₁ 𝔭₂ : Ideal (𝓞 K))
    (h𝔭₁ : 𝔭₁.IsPrime) (h𝔭₂ : 𝔭₂.IsPrime) (hne : 𝔭₁ ≠ 𝔭₂)
    (hN₁ : Ideal.absNorm 𝔭₁ = p) (hN₂ : Ideal.absNorm 𝔭₂ = p)
    (hsplit : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) = 𝔭₁ * 𝔭₂)
    (k : ℕ) :
    idealNormCount K (p ^ (k + 1)) = idealNormCount K (p ^ k) + 1 := by
  rw [idealNormCount_split_pow K hp 𝔭₁ 𝔭₂ h𝔭₁ h𝔭₂ hne hN₁ hN₂ hsplit (k + 1),
      idealNormCount_split_pow K hp 𝔭₁ 𝔭₂ h𝔭₁ h𝔭₂ hne hN₁ hN₂ hsplit k]

/-! ### Inert and ramified prime-power counts

These helpers cover the two remaining local cases needed for Hecke
factorizations over real quadratic fields (and any number field where
a rational prime has a unique prime above with explicit norm relation).
-/

/-! Two specializations: inert (norm of unique prime is p^2, so ⟨p⟩ = 𝔭),
and ramified (norm is p, so ⟨p⟩ = 𝔭^2). -/

/-- **Inert prime-power count.** If `p` is a rational prime, `𝔭` is a
prime ideal with `absNorm 𝔭 = p^2` and `⟨p⟩ = 𝔭` in `𝓞 K`, then
`idealNormCount K (p^k) = 1` if `k` is even, else `0`. -/
theorem idealNormCount_inert_prime_pow {p : ℕ} (hp : p.Prime)
    (𝔭 : Ideal (𝓞 K)) (h𝔭_prime : 𝔭.IsPrime)
    (h𝔭_norm : Ideal.absNorm 𝔭 = p ^ 2)
    (hpO : Ideal.span ({(p : 𝓞 K)} : Set _) = 𝔭) (k : ℕ) :
    idealNormCount K (p ^ k) = if Even k then 1 else 0 := by
  classical
  have hp_ne : (p : ℕ) ≠ 0 := hp.ne_zero
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero _ hp_ne
  have h𝔭_ne : 𝔭 ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at h𝔭_norm
    exact (pow_ne_zero 2 hp_ne) h𝔭_norm.symm
  have h𝔭_prime' : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭_ne h𝔭_prime
  rw [idealNormCount_apply_of_ne_zero K hpk_ne]
  -- Claim: {I : absNorm I = p^k} is in bijection with {j : 2j = k} (one element if k even, none if odd).
  -- Helper closure: any ideal `I` with `absNorm I = p^N` equals `𝔭 ^ j` for some `j`
  -- with `2 * j = N`.
  have key : ∀ {N : ℕ} {I : Ideal (𝓞 K)}, Ideal.absNorm I = p ^ N →
      ∃ j, 2 * j = N ∧ I = 𝔭 ^ j := by
    intro N I hI
    have hpN_ne : p ^ N ≠ 0 := pow_ne_zero _ hp_ne
    have hI_ne : I ≠ ⊥ := by
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      exact hpN_ne hI.symm
    have hpk_mem : ((p : 𝓞 K) ^ N) ∈ I := by
      have := Ideal.absNorm_mem I
      rw [hI] at this
      exact_mod_cast this
    have hI_dvd_pk : I ∣ Ideal.span ({(p : 𝓞 K) ^ N} : Set (𝓞 K)) := by
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]; exact hpk_mem
    have hspan_pow : Ideal.span ({(p : 𝓞 K) ^ N} : Set (𝓞 K)) = 𝔭 ^ N := by
      rw [← hpO, Ideal.span_singleton_pow]
    rw [hspan_pow] at hI_dvd_pk
    have hpow_ne : (𝔭 ^ N : Ideal (𝓞 K)) ≠ 0 := pow_ne_zero _ h𝔭_ne
    have hfac_le :
        UniqueFactorizationMonoid.normalizedFactors I ≤
          UniqueFactorizationMonoid.normalizedFactors (𝔭 ^ N) :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI_ne hpow_ne).mp
        hI_dvd_pk
    have hRHS :
        UniqueFactorizationMonoid.normalizedFactors (𝔭 ^ N) =
          N • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭_prime'.irreducible,
          normalize_eq]
    set j := Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors I) with hj_def
    have hfac_eq :
        UniqueFactorizationMonoid.normalizedFactors I =
          j • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
      refine Multiset.ext.mpr fun q => ?_
      by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors I
      · have hq_in : q ∈ N • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
          rw [← hRHS]; exact Multiset.mem_of_le hfac_le hq
        simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hq_in
        obtain ⟨_, rfl⟩ := hq_in
        rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
      · rw [Multiset.count_eq_zero.mpr hq, Multiset.count_nsmul]
        by_cases hq1 : q = 𝔭
        · subst hq1
          have : j = 0 := by rw [hj_def]; exact Multiset.count_eq_zero.mpr hq
          rw [this, Nat.zero_mul]
        · rw [Multiset.count_singleton, if_neg hq1, mul_zero]
    have hI_eq : I = 𝔭 ^ j := by
      have hprod : (UniqueFactorizationMonoid.normalizedFactors I).prod = I := by
        rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hI_ne, normalize_eq]
      rw [← hprod, hfac_eq, Multiset.prod_nsmul, Multiset.prod_singleton]
    have h2j_eq : 2 * j = N := by
      have hnorm : Ideal.absNorm (𝔭 ^ j) = p ^ N := by rw [← hI_eq]; exact hI
      rw [map_pow, h𝔭_norm, ← pow_mul] at hnorm
      exact Nat.pow_right_injective hp.two_le hnorm
    exact ⟨j, h2j_eq, hI_eq⟩
  by_cases hke : Even k
  · obtain ⟨m, rfl⟩ := hke
    rw [if_pos ⟨m, rfl⟩, Nat.card_eq_one_iff_exists]
    refine ⟨⟨𝔭 ^ m, by rw [map_pow, h𝔭_norm]; ring⟩, ?_⟩
    rintro ⟨I, hI⟩
    apply Subtype.ext
    obtain ⟨j, h2j, hIeq⟩ := key hI
    have hjm : j = m := by omega
    subst hjm
    exact hIeq
  · rw [if_neg hke, Nat.card_eq_zero]
    refine Or.inl ⟨?_⟩
    rintro ⟨I, hI⟩
    obtain ⟨j, h2j, _⟩ := key hI
    exact hke ⟨j, by omega⟩

/-- **Unique-prime-above (ramified) prime-power count.** If `p` is a
rational prime, `𝔭` is a prime ideal with `absNorm 𝔭 = p` and
`⟨p⟩ = 𝔭^2` in `𝓞 K`, then `idealNormCount K (p^k) = 1` for all `k`. -/
theorem idealNormCount_unique_prime_above {p : ℕ} (hp : p.Prime)
    (𝔭 : Ideal (𝓞 K)) (h𝔭_prime : 𝔭.IsPrime)
    (h𝔭_norm : Ideal.absNorm 𝔭 = p)
    (hpO : Ideal.span ({(p : 𝓞 K)} : Set _) = 𝔭 ^ 2) (k : ℕ) :
    idealNormCount K (p ^ k) = 1 := by
  classical
  have hp_ne : (p : ℕ) ≠ 0 := hp.ne_zero
  have hpk_ne : p ^ k ≠ 0 := pow_ne_zero _ hp_ne
  have h𝔭_ne : 𝔭 ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at h𝔭_norm
    exact hp_ne h𝔭_norm.symm
  have h𝔭_prime' : Prime 𝔭 := Ideal.prime_of_isPrime h𝔭_ne h𝔭_prime
  rw [idealNormCount_apply_of_ne_zero K hpk_ne]
  -- Helper: any ideal of norm `p^N` is `𝔭 ^ j` with `j = N`.
  have key : ∀ {N : ℕ} {I : Ideal (𝓞 K)}, Ideal.absNorm I = p ^ N → I = 𝔭 ^ N := by
    intro N I hI
    have hpN_ne : p ^ N ≠ 0 := pow_ne_zero _ hp_ne
    have hI_ne : I ≠ ⊥ := by
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      exact hpN_ne hI.symm
    have hpk_mem : ((p : 𝓞 K) ^ N) ∈ I := by
      have := Ideal.absNorm_mem I
      rw [hI] at this
      exact_mod_cast this
    have hI_dvd_pk : I ∣ Ideal.span ({(p : 𝓞 K) ^ N} : Set (𝓞 K)) := by
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]; exact hpk_mem
    have hspan_pow : Ideal.span ({(p : 𝓞 K) ^ N} : Set (𝓞 K)) = 𝔭 ^ (2 * N) := by
      rw [← Ideal.span_singleton_pow, hpO, ← pow_mul, mul_comm]
    rw [hspan_pow] at hI_dvd_pk
    have hpow_ne : (𝔭 ^ (2 * N) : Ideal (𝓞 K)) ≠ 0 := pow_ne_zero _ h𝔭_ne
    have hfac_le :
        UniqueFactorizationMonoid.normalizedFactors I ≤
          UniqueFactorizationMonoid.normalizedFactors (𝔭 ^ (2 * N)) :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI_ne hpow_ne).mp
        hI_dvd_pk
    have hRHS :
        UniqueFactorizationMonoid.normalizedFactors (𝔭 ^ (2 * N)) =
          (2 * N) • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭_prime'.irreducible,
          normalize_eq]
    set j := Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors I) with hj_def
    have hfac_eq :
        UniqueFactorizationMonoid.normalizedFactors I =
          j • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
      refine Multiset.ext.mpr fun q => ?_
      by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors I
      · have hq_in : q ∈ (2 * N) • ({𝔭} : Multiset (Ideal (𝓞 K))) := by
          rw [← hRHS]; exact Multiset.mem_of_le hfac_le hq
        simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hq_in
        obtain ⟨_, rfl⟩ := hq_in
        rw [Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
      · rw [Multiset.count_eq_zero.mpr hq, Multiset.count_nsmul]
        by_cases hq1 : q = 𝔭
        · subst hq1
          have : j = 0 := by rw [hj_def]; exact Multiset.count_eq_zero.mpr hq
          rw [this, Nat.zero_mul]
        · rw [Multiset.count_singleton, if_neg hq1, mul_zero]
    have hI_eq : I = 𝔭 ^ j := by
      have hprod : (UniqueFactorizationMonoid.normalizedFactors I).prod = I := by
        rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hI_ne, normalize_eq]
      rw [← hprod, hfac_eq, Multiset.prod_nsmul, Multiset.prod_singleton]
    have hjN : j = N := by
      have hnorm : Ideal.absNorm (𝔭 ^ j) = p ^ N := by rw [← hI_eq]; exact hI
      rw [map_pow, h𝔭_norm] at hnorm
      exact Nat.pow_right_injective hp.two_le hnorm
    rw [hI_eq, hjN]
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨𝔭 ^ k, by rw [map_pow, h𝔭_norm]⟩, ?_⟩
  rintro ⟨I, hI⟩
  exact Subtype.ext (key hI)

/-- **PID element-count to ideal-count bridge (subtype form).**

For a number field `K` whose ring of integers `𝓞 K` is a PID, ideals of
norm `n ≥ 1` are in bijection with associate classes of elements of norm
`n`.  Concretely: if `S` is a set of representatives — one per associate
class — of elements `α ∈ 𝓞 K` with `Ideal.absNorm (Ideal.span {α}) = n`,
then `Nat.card S = idealNormCount K n`.

We package this as: a bijection between any chosen set of associate-class
representatives and the norm fiber of ideals.

TODO Phase 3a: in a PID, every ideal is principal `⟨α⟩`, and
`⟨α⟩ = ⟨β⟩ ↔ α ~ β` (associate).  Bijection: `α ↦ ⟨α⟩`. -/
theorem idealNormCount_eq_of_principal_repr [IsPrincipalIdealRing (𝓞 K)]
    {n : ℕ} (hn : n ≠ 0)
    (S : Set (𝓞 K))
    (hS_norm : ∀ α ∈ S, Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) = n)
    (hS_inj : ∀ α ∈ S, ∀ β ∈ S,
      Ideal.span ({α} : Set (𝓞 K)) = Ideal.span ({β} : Set (𝓞 K)) → α = β)
    (hS_surj : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n →
      ∃ α ∈ S, I = Ideal.span ({α} : Set (𝓞 K))) :
    Nat.card S = idealNormCount K n := by
  rw [idealNormCount_apply_of_ne_zero K hn]
  -- Build a bijection S ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  -- via α ↦ ⟨Ideal.span {α}, hS_norm α _⟩.
  let f : S → {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun α => ⟨Ideal.span ({α.1} : Set (𝓞 K)), hS_norm α.1 α.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro α β hfab
    have heq : Ideal.span ({α.1} : Set (𝓞 K)) = Ideal.span ({β.1} : Set (𝓞 K)) := by
      simpa [f] using congrArg Subtype.val hfab
    exact Subtype.ext (hS_inj α.1 α.2 β.1 β.2 heq)
  · rintro ⟨I, hI⟩
    obtain ⟨α, hαS, hIα⟩ := hS_surj I hI
    exact ⟨⟨α, hαS⟩, by simp [f, hIα]⟩

end NumberField
