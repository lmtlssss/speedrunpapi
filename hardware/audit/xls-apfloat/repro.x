// Four cases in XLS's apfloat library, as DSLX tests. Each one fails at the pinned release.
import apfloat;
import float32;

type F32 = float32::F32;

// fma with a NaN operand, 4 exponent bits and 3 fraction bits (the E4M3 layout): the result is +inf.
#[test]
fn fma_nan_three_fraction_bits() {
    let nan = apfloat::qnan<u32:4, u32:3>();
    let one = apfloat::one<u32:4, u32:3>(u1:0);
    let r = apfloat::fma(nan, one, one);
    assert_eq(apfloat::is_nan(r), true);
}

// fma with a NaN operand in binary32: the result is not qnan().
#[test]
fn fma_nan_binary32() {
    let nan = apfloat::qnan<u32:8, u32:23>();
    let one = apfloat::one<u32:8, u32:23>(u1:0);
    assert_eq(apfloat::fma(nan, one, one), nan);
}

// (1 * -0) + -0 is -0; add(-0, -0) returns it, fma returns +0.
#[test]
fn fma_negative_zero() {
    let one = apfloat::one<u32:8, u32:23>(u1:0);
    let nz = apfloat::zero<u32:8, u32:23>(u1:1);
    assert_eq(apfloat::add(nz, nz), nz);
    assert_eq(apfloat::fma(one, nz, nz), nz);
}

// 100000 to binary16, rounding toward zero: the largest finite number, 65504, not infinity.
#[test]
fn from_fixed_rz_overflow() {
    let r = apfloat::cast_from_fixed_using_rz<u32:5, u32:10, u32:32>(s32:100000);
    assert_eq(apfloat::is_inf(r), false);
}
