import EthFollowup.Primes.CoprimeNodeDesc

/-! Canonical bounded Bezout witnesses include the residue 1. The modulus-1
case is a separate, unique boundary case for the Ramanujan sum. -/
namespace EthFollowup.Primes.CoprimeNode

theorem certificate_exists_of_one_le {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hc : a.Coprime b) : ∃ u v, Certificate a b u v := by
  by_cases h : a = 1
  · subst a
    exact ⟨1, 0, by unfold Certificate; omega⟩
  · exact certificate_exists (by omega) hb hc

theorem certificate_existsUnique_of_one_le {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hc : a.Coprime b) : ∃! uv : ℕ × ℕ, Certificate a b uv.1 uv.2 := by
  obtain ⟨u,v,h⟩ := certificate_exists_of_one_le ha hb hc
  refine ⟨(u,v),h,?_⟩
  intro uv huv
  obtain ⟨h1,h2⟩ := huv.unique (by omega : 0 < b) h
  exact Prod.ext h1 h2

theorem residue_coprime_iff {a b : ℕ} (hb : 2 ≤ b) :
    a.Coprime b ↔ 1 ≤ a ∧ ∃ u v, Certificate a b u v := by
  constructor
  · intro hc
    have ha : 1 ≤ a := by
      by_contra h
      have : a = 0 := by omega
      subst a
      simp at hc
      omega
    exact ⟨ha, certificate_exists_of_one_le ha hb hc⟩
  · rintro ⟨_,u,v,h⟩
    exact h.coprime

theorem residue_modulus_one (a : ℕ) :
    a < 1 ∧ a.Coprime 1 ↔ a = 0 := by simp

end EthFollowup.Primes.CoprimeNode
