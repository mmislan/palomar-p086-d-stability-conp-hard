# Claim correspondence

The submission concerns the explicit reduction underlying the companion manuscript's coNP-hardness theorem.

| Formal endpoint | Content | Manuscript |
|---|---|---|
| `DStabilityHardness.dStability_coNP_reduction` | Pell-search bound, denominator bound, integer-entry bound, D-stability iff no equal split, and strict D-instability for an equal split | Sections 4–5 and 7 |
| `DStabilityHardness.partition_dichotomy` | The same bounds together with D-stability and D-semistability for no-instances, and strict D-instability and failure of both stability properties for yes-instances | Sections 5 and 7 |

The input is a positive natural-number weight function on an arbitrary nonempty finite index type, with total weight 2T. The output is the literal integer matrix `hardIntMatrix` on `Fin 4 ⊕ κ`, cast entrywise to the reals. `DStable` quantifies over every positive right diagonal scaling; `DUnstable` requires an eigenvalue in the open right half-plane. `DNonUnstable` allows eigenvalues on the imaginary axis. Right and left positive diagonal scalings are similar, as explained in Section 2.

For N = max(8T, 4), the selected statements bound the first qualifying Pell index by log₃ N + 1, its denominator q by 4N + 1, and every output entry by 720q³T. The input hypotheses imply T > 0. They admit both yes- and no-instances: weights (1,1) and (1,3) have totals 2 and 4, respectively. These examples are elementary witnesses, not additional selected Lean declarations.

The complexity conclusion uses the classical NP-completeness of PARTITION and the conventional bit-operation analysis and trivial-input handling in Section 5. The selected Lean statements certify the mathematical reduction and size bounds. The reduction gives binary-encoding hardness; it does not establish strong hardness or membership in coNP.

Chen, Fan and Yu's [1995 paper](https://doi.org/10.1016/0167-6911%2894%2900036-U) motivates the computational question. Its structured-singular-value formulation is not used as a substitute for the explicit reduction.
