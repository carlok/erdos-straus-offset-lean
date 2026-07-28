# Public-core selection

## Public declarations

### Representation and construction

- `IsES`
- `isES_of_polynomial`
- `isES_of_offset_certificate`
- `second_divisibility`
- `constructive_offset`

### Admissibility

- `offsetX`
- `offsetB`
- `OffsetAdmissible`
- `OffsetAdmissible.isES`
- `OffsetAdmissible.add_period`

### Exact period structure

- `offsetX_add_general`
- `offsetB_add_general`
- `poly_dvd_all`
- `OffsetAdmissible.all_add_mul_iff`
- `OffsetAdmissible.period_dvd`
- `OffsetAdmissible.all_add_mul_iff_period_dvd`
- `OffsetAdmissible.least_positive_period`

## Private implementation lemmas

- `sq_nezero_int`
- `unified_offset_theorem`
- `offsetX_add_period`
- `offsetB_add_period`
- `offsetB_add_four_mul`
- `prime_dvd_step_of_forall_not_dvd`
- `divisor_dvd_quarter_step`

These are retained only because the selected public proofs use them. They are
not proposed as permanent public API.

## Excluded material

The draft contains no:

- `example` declarations;
- explicit `d = 2` or `d = 5` seed families;
- `mordell_3mod4` or `family_I`;
- `fixed_d_progression` convenience wrappers;
- tautological polynomial theorem;
- TeX, empirical, density, coverage, or novelty-priority claim.

