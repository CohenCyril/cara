# Changelog (unreleased)

## [Unreleased]

### Added

- in `sequences.v`:
  + lemma `dvg_harmonic`
- new file `nsatz_realType`
- new file `exp.v`
  + definition `diffs`
  + lemmas `diffsN`, `diffs_sumE`, `diffs_equiv`, `cvg_diffs_equiv`, `termdiff`
  + lemmas `expR0`, `expR_gt0`, `expRN`, `expRD`, `expRMm`
  + lemmas `expR_gt1`, `expR_lt1, `expRB`, `ltr_expR`, `ler_expR`, `expR_inj`,
    `expR_total_gt1`, `expR_total`
  + definition `ln`
  + lemmas `expK`, `lnK`, `ln1`, `lnM`, `ln_inj`, `lnV`, `ln_div`, `ltr_ln`, `ler_ln`, `lnX`
  + lemmas `le_ln1Dx`, `ln_sublinear`, `ln_ge0`, `ln_gt0`
  + definition `exp_fun`, notation `^
  + lemmas `exp_fun_gt0`, `exp_funr1`, `exp_funr0`, `exp_fun1`, `ler_exp_fun`,
    `exp_funD`, `exp_fun_inv`, `exp_fun_mulrn`
  + definition `riemannR`, lemmas `riemannR_gt0`, `dvg_riemannR`
- new file `trigo.v`
  + definitions `periodic`, `alternating`
  + lemmas `periodicn`, `alternatingn`
  + definition `sin`
  + lemma `sin0`
  + definition `cos`
  + lemmas `cos0`
  + lemmas `continuous_sin`, `continuous_cos`
  + lemmas `cos2Dsin2`, `cosD`, `sinN`, `sinB`
  + definition `pi`
  + lemmas `pihalfE`, `cos2_lt0`, `cos_exists`
  + lemmas `pi_gt0`, `pi_ge0`
  + lemmas `cos_inj`, `sin_inj`, `ltr_cos`, `ltr_sin`
  + definition `tan`
  + lemmas `tan0`, `tanpi`
  + lemmas `tanN`, `tanD`, `tan_mulr2n`, `cos2_tan2`
  + lemmas `tan_pihalf`, `tan_piquarter`, `tanDpi`, `continuous_tan`
  + instance `is_derive_tan`
  + lemmas `derivable_tan`, `ltr_tan`, `tan_inj`
  + definition `acos`
  + lemmas `acosK`, `cosK`
  + definition `asin`
  + lemmas `asinK`, `sinK`
  + definition `atan`
  + lemmas `atanK`, `tanK`

### Changed

### Renamed

### Removed

- in `sequences.v`:
  + lemma `iter_addr`

### Infrastructure

### Misc
