# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`
  + definitions `isSemiRingOfSets`, `SemiRingOfSets`, notation `semiRingOfSetsType`
  + definitions `RingOfSets_from_semiRingOfSets`, `RingOfSets`, notation `ringOfSetsType`
  + factory: `isRingOfSets`
  + definitions `Measurable_from_ringOfSets`, `Measurable`
  + lemma `semiRingOfSets_measurable{I,D}`
  + definition `diff_fsets`, lemmas `semiRingOfSets_diff_fsetsE`, `semiRingOfSets_diff_fsets_disjoint`
  + definitions `isMeasurable`
  + factory: `isMeasurable`
  + lemma `bigsetU_measurable`, `measurable_bigcap`
  + definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`
  + lemmas `semi_additive2P`, `semi_additiveE`, `semi_additive2E`,
    `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`
  + `Module AdditiveMeasure`
     * notations `additive_measure`, `{additive_measure set T -> {ereal R}}`
  + lemmas `measure_semi_additive2`, `measure_semi_additive`, `measure_semi_sigma_additive`
  + lemma `semi_sigma_additive_is_additive`, canonical/coercion `measure_additive_measure`
  + lemma `sigma_additive_is_additive`
  + notations `ringOfSetsType`, `outer_measure`
  + definition `negligible` and its notation `.-negligible`
  + lemmas `negligibleP`, `negligible_set0`
  + definition `almost_everywhere` and its notation `{ae mu, P}`
  + lemma `satisfied_almost_everywhere`
  + definition `sigma_subadditive`
  + `Module OuterMeasure`
    * notation `outer_measure`, `{outer_measure set T -> {ereal R}}`
  + lemmas `outer_measure0`, `outer_measure_ge0`, `le_outer_measure`,
    `outer_measure_sigma_subadditive`, `le_outer_measureIC`

### Changed

### Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`
- in `measure.v`:
  + `sigma_additive_implies_additive` -> `sigma_additive_is_additive`

### Removed

### Infrastructure

### Misc
