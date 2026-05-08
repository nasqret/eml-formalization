import EML.Framework.Complex.Subst
import EML.Framework.Complex.Builders.Trig

/-!
# Periodicity infrastructure for trig witnesses (Plan C)

Foundational shift terms for the multi-witness periodicity approach to
full-real-domain trig. See [`Periodicity.md`](./Periodicity.md) for the
full implementation spec — concrete Lean code with proof outlines and
estimated effort per piece.

## Status

- ✅ **Foundation:** `EMLTermℂ.subst0` + `eval?_subst0` (in `Subst.lean`)
- ✅ **`2π` term:** `twoPiPubℂ` definition (this file)
- ⏳ **`2π` eval lemma:** the `eval?_twoPiPubℂ` proof — requires
  discharging `mkMulℂ`'s `ADDsafeℂ` bundle (8 conditions on
  imaginary components) for the real-valued `log 2` and `log π`.
  Concrete proof outline in `Periodicity.md` §"Implementation order".
- ⏳ **Shift terms:** `shiftSub2πℂ`, `shiftAdd2πℂ`.
- ⏳ **Witness families:** `sin_witness_family`, `arctan_witness_family`,
  `tan_witness_family`.

## Why this file is currently a stub

The `eval?_twoPiPubℂ` lemma's proof is mechanical (~50 lines of `.im =
0` discharges for real-valued log arguments) but iterating each step
through the build cycle is multi-hour work that's better gated by
GPT Pro's recommendation between Path A and Path C — see
[`gpt_pro_bundle/trig_widening/`](../../../../../../../gpt_pro_bundle/trig_widening/).

If Pro recommends Path C, the next session lifts the `Periodicity.md`
spec into compiling Lean. If Pro recommends Path A or some path we
hadn't considered, this file gets revised to match.

The definition itself is uncontroversial regardless of path choice —
`twoPiPubℂ = mkMulℂ twoPubℂ piPubℂ` is the natural complex constant
for `2π` and will be needed in any path involving period-`2π` shifts.
-/

namespace EML

/-! ## §C.1 — The constant `2π` as an `EMLTermℂ` -/

/-- The complex constant `2π` as an `EMLTermℂ`, built as `mkMulℂ` of
the public `2` and `π` terms. Total tree size is `K(twoPubℂ) +
K(piPubℂ) + K(mkMulℂ-overhead) ≈ 19 + 233 + 250 ≈ 502` nodes. -/
noncomputable def twoPiPubℂ : EMLTermℂ := mkMulℂ twoPubℂ piPubℂ

end EML
