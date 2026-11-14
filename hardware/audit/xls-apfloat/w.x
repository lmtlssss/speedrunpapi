import apfloat;

pub fn add_3_2(a: uN[6], b: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::add<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)))
}

pub fn addlza_3_2(a: uN[6], b: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::add<u32:3, u32:2, true>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)))
}

pub fn sub_3_2(a: uN[6], b: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::sub<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)))
}

pub fn mul_3_2(a: uN[6], b: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::mul<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)))
}

pub fn fma_3_2(a: uN[6], b: uN[6], c: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::fma<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b), apfloat::unflatten<u32:3, u32:2>(c)))
}

pub fn ceil_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::ceil_with_denorms<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn ceildaz_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::ceil_daz<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn floor_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::floor_with_denorms<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn floordaz_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::floor_daz<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn trunc_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::trunc<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn round_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::round<u32:3, u32:2, apfloat::RoundStyle::TIES_TO_EVEN>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn rounda_3_2(a: uN[6]) -> uN[6] {
    apfloat::flatten(apfloat::round<u32:3, u32:2, apfloat::RoundStyle::TIES_TO_AWAY>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn eq_3_2(a: uN[6], b: uN[6]) -> uN[1] {
    apfloat::eq_2<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)) as uN[1]
}

pub fn gt_3_2(a: uN[6], b: uN[6]) -> uN[1] {
    apfloat::gt_2<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)) as uN[1]
}

pub fn gte_3_2(a: uN[6], b: uN[6]) -> uN[1] {
    apfloat::gte_2<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)) as uN[1]
}

pub fn lte_3_2(a: uN[6], b: uN[6]) -> uN[1] {
    apfloat::lte_2<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)) as uN[1]
}

pub fn lt_3_2(a: uN[6], b: uN[6]) -> uN[1] {
    apfloat::lt_2<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), apfloat::unflatten<u32:3, u32:2>(b)) as uN[1]
}

pub fn toint_3_2_4(a: uN[6]) -> uN[4] {
    apfloat::to_int<u32:3, u32:2, u32:4>(apfloat::unflatten<u32:3, u32:2>(a)) as uN[4]
}

pub fn touint_3_2_4(a: uN[6]) -> uN[4] {
    apfloat::to_uint<u32:4, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a))
}

pub fn tofixed_3_2_4(a: uN[6]) -> uN[4] {
    apfloat::cast_to_fixed<u32:4, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)) as uN[4]
}

pub fn toint_3_2_8(a: uN[6]) -> uN[8] {
    apfloat::to_int<u32:3, u32:2, u32:8>(apfloat::unflatten<u32:3, u32:2>(a)) as uN[8]
}

pub fn touint_3_2_8(a: uN[6]) -> uN[8] {
    apfloat::to_uint<u32:8, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a))
}

pub fn tofixed_3_2_8(a: uN[6]) -> uN[8] {
    apfloat::cast_to_fixed<u32:8, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)) as uN[8]
}

pub fn fromfixed_rne_3_2_8(x: sN[8]) -> uN[6] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:3, u32:2, u32:8>(x))
}

pub fn fromfixed_rz_3_2_8(x: sN[8]) -> uN[6] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:3, u32:2, u32:8>(x))
}

pub fn fromfixed_rne_3_2_12(x: sN[12]) -> uN[6] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:3, u32:2, u32:12>(x))
}

pub fn fromfixed_rz_3_2_12(x: sN[12]) -> uN[6] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:3, u32:2, u32:12>(x))
}

pub fn ldexp_3_2(a: uN[6], e: sN[8]) -> uN[6] {
    apfloat::flatten(apfloat::ldexp<u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a), e as s32))
}

pub fn down_rne_5_6_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast_rne<u32:2, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a)))
}

pub fn down_even_5_6_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_5_6_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_3_2_to_5_6(a: uN[6]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:5, u32:6, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn updaz_3_2_to_5_6(a: uN[6]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:5, u32:6, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn down_rne_4_7_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast_rne<u32:2, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a)))
}

pub fn down_even_4_7_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_4_7_to_3_2(a: uN[12]) -> uN[6] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_3_2_to_4_7(a: uN[6]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:4, u32:7, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn updaz_3_2_to_4_7(a: uN[6]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:4, u32:7, u32:3, u32:2>(apfloat::unflatten<u32:3, u32:2>(a)))
}

pub fn add_4_3(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)))
}

pub fn addlza_4_3(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:4, u32:3, true>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)))
}

pub fn sub_4_3(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::sub<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)))
}

pub fn mul_4_3(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::mul<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)))
}

pub fn fma_4_3(a: uN[8], b: uN[8], c: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::fma<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b), apfloat::unflatten<u32:4, u32:3>(c)))
}

pub fn ceil_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_with_denorms<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn ceildaz_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_daz<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn floor_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_with_denorms<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn floordaz_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_daz<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn trunc_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::trunc<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn round_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:4, u32:3, apfloat::RoundStyle::TIES_TO_EVEN>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn rounda_4_3(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:4, u32:3, apfloat::RoundStyle::TIES_TO_AWAY>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn eq_4_3(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::eq_2<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)) as uN[1]
}

pub fn gt_4_3(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gt_2<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)) as uN[1]
}

pub fn gte_4_3(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gte_2<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)) as uN[1]
}

pub fn lte_4_3(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lte_2<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)) as uN[1]
}

pub fn lt_4_3(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lt_2<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), apfloat::unflatten<u32:4, u32:3>(b)) as uN[1]
}

pub fn toint_4_3_4(a: uN[8]) -> uN[4] {
    apfloat::to_int<u32:4, u32:3, u32:4>(apfloat::unflatten<u32:4, u32:3>(a)) as uN[4]
}

pub fn touint_4_3_4(a: uN[8]) -> uN[4] {
    apfloat::to_uint<u32:4, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a))
}

pub fn tofixed_4_3_4(a: uN[8]) -> uN[4] {
    apfloat::cast_to_fixed<u32:4, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)) as uN[4]
}

pub fn toint_4_3_8(a: uN[8]) -> uN[8] {
    apfloat::to_int<u32:4, u32:3, u32:8>(apfloat::unflatten<u32:4, u32:3>(a)) as uN[8]
}

pub fn touint_4_3_8(a: uN[8]) -> uN[8] {
    apfloat::to_uint<u32:8, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a))
}

pub fn tofixed_4_3_8(a: uN[8]) -> uN[8] {
    apfloat::cast_to_fixed<u32:8, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)) as uN[8]
}

pub fn fromfixed_rne_4_3_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:4, u32:3, u32:8>(x))
}

pub fn fromfixed_rz_4_3_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:4, u32:3, u32:8>(x))
}

pub fn fromfixed_rne_4_3_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:4, u32:3, u32:12>(x))
}

pub fn fromfixed_rz_4_3_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:4, u32:3, u32:12>(x))
}

pub fn ldexp_4_3(a: uN[8], e: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ldexp<u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a), e as s32))
}

pub fn down_rne_5_6_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast_rne<u32:3, u32:4, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a)))
}

pub fn down_even_5_6_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:3, u32:4, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_5_6_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:3, u32:4, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_4_3_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:5, u32:6, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn updaz_4_3_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:5, u32:6, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn down_rne_4_7_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast_rne<u32:3, u32:4, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a)))
}

pub fn down_even_4_7_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:3, u32:4, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_4_7_to_4_3(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:3, u32:4, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_4_3_to_4_7(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:4, u32:7, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn updaz_4_3_to_4_7(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:4, u32:7, u32:4, u32:3>(apfloat::unflatten<u32:4, u32:3>(a)))
}

pub fn add_3_4(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)))
}

pub fn addlza_3_4(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:3, u32:4, true>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)))
}

pub fn sub_3_4(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::sub<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)))
}

pub fn mul_3_4(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::mul<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)))
}

pub fn fma_3_4(a: uN[8], b: uN[8], c: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::fma<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b), apfloat::unflatten<u32:3, u32:4>(c)))
}

pub fn ceil_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_with_denorms<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn ceildaz_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_daz<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn floor_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_with_denorms<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn floordaz_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_daz<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn trunc_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::trunc<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn round_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:3, u32:4, apfloat::RoundStyle::TIES_TO_EVEN>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn rounda_3_4(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:3, u32:4, apfloat::RoundStyle::TIES_TO_AWAY>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn eq_3_4(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::eq_2<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)) as uN[1]
}

pub fn gt_3_4(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gt_2<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)) as uN[1]
}

pub fn gte_3_4(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gte_2<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)) as uN[1]
}

pub fn lte_3_4(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lte_2<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)) as uN[1]
}

pub fn lt_3_4(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lt_2<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), apfloat::unflatten<u32:3, u32:4>(b)) as uN[1]
}

pub fn toint_3_4_4(a: uN[8]) -> uN[4] {
    apfloat::to_int<u32:3, u32:4, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)) as uN[4]
}

pub fn touint_3_4_4(a: uN[8]) -> uN[4] {
    apfloat::to_uint<u32:4, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a))
}

pub fn tofixed_3_4_4(a: uN[8]) -> uN[4] {
    apfloat::cast_to_fixed<u32:4, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)) as uN[4]
}

pub fn toint_3_4_8(a: uN[8]) -> uN[8] {
    apfloat::to_int<u32:3, u32:4, u32:8>(apfloat::unflatten<u32:3, u32:4>(a)) as uN[8]
}

pub fn touint_3_4_8(a: uN[8]) -> uN[8] {
    apfloat::to_uint<u32:8, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a))
}

pub fn tofixed_3_4_8(a: uN[8]) -> uN[8] {
    apfloat::cast_to_fixed<u32:8, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)) as uN[8]
}

pub fn fromfixed_rne_3_4_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:3, u32:4, u32:8>(x))
}

pub fn fromfixed_rz_3_4_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:3, u32:4, u32:8>(x))
}

pub fn fromfixed_rne_3_4_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:3, u32:4, u32:12>(x))
}

pub fn fromfixed_rz_3_4_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:3, u32:4, u32:12>(x))
}

pub fn ldexp_3_4(a: uN[8], e: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ldexp<u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a), e as s32))
}

pub fn down_rne_5_6_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast_rne<u32:4, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a)))
}

pub fn down_even_5_6_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:4, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_5_6_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:4, u32:3, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_3_4_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:5, u32:6, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn updaz_3_4_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:5, u32:6, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn down_rne_4_7_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast_rne<u32:4, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a)))
}

pub fn down_even_4_7_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:4, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_4_7_to_3_4(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:4, u32:3, u32:7, u32:4>(apfloat::unflatten<u32:4, u32:7>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_3_4_to_4_7(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:4, u32:7, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn updaz_3_4_to_4_7(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:4, u32:7, u32:3, u32:4>(apfloat::unflatten<u32:3, u32:4>(a)))
}

pub fn add_5_2(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)))
}

pub fn addlza_5_2(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::add<u32:5, u32:2, true>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)))
}

pub fn sub_5_2(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::sub<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)))
}

pub fn mul_5_2(a: uN[8], b: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::mul<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)))
}

pub fn fma_5_2(a: uN[8], b: uN[8], c: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::fma<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b), apfloat::unflatten<u32:5, u32:2>(c)))
}

pub fn ceil_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_with_denorms<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn ceildaz_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ceil_daz<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn floor_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_with_denorms<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn floordaz_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::floor_daz<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn trunc_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::trunc<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn round_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:5, u32:2, apfloat::RoundStyle::TIES_TO_EVEN>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn rounda_5_2(a: uN[8]) -> uN[8] {
    apfloat::flatten(apfloat::round<u32:5, u32:2, apfloat::RoundStyle::TIES_TO_AWAY>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn eq_5_2(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::eq_2<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)) as uN[1]
}

pub fn gt_5_2(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gt_2<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)) as uN[1]
}

pub fn gte_5_2(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::gte_2<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)) as uN[1]
}

pub fn lte_5_2(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lte_2<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)) as uN[1]
}

pub fn lt_5_2(a: uN[8], b: uN[8]) -> uN[1] {
    apfloat::lt_2<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), apfloat::unflatten<u32:5, u32:2>(b)) as uN[1]
}

pub fn toint_5_2_4(a: uN[8]) -> uN[4] {
    apfloat::to_int<u32:5, u32:2, u32:4>(apfloat::unflatten<u32:5, u32:2>(a)) as uN[4]
}

pub fn touint_5_2_4(a: uN[8]) -> uN[4] {
    apfloat::to_uint<u32:4, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a))
}

pub fn tofixed_5_2_4(a: uN[8]) -> uN[4] {
    apfloat::cast_to_fixed<u32:4, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)) as uN[4]
}

pub fn toint_5_2_8(a: uN[8]) -> uN[8] {
    apfloat::to_int<u32:5, u32:2, u32:8>(apfloat::unflatten<u32:5, u32:2>(a)) as uN[8]
}

pub fn touint_5_2_8(a: uN[8]) -> uN[8] {
    apfloat::to_uint<u32:8, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a))
}

pub fn tofixed_5_2_8(a: uN[8]) -> uN[8] {
    apfloat::cast_to_fixed<u32:8, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)) as uN[8]
}

pub fn fromfixed_rne_5_2_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:5, u32:2, u32:8>(x))
}

pub fn fromfixed_rz_5_2_8(x: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:5, u32:2, u32:8>(x))
}

pub fn fromfixed_rne_5_2_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rne<u32:5, u32:2, u32:12>(x))
}

pub fn fromfixed_rz_5_2_12(x: sN[12]) -> uN[8] {
    apfloat::flatten(apfloat::cast_from_fixed_using_rz<u32:5, u32:2, u32:12>(x))
}

pub fn ldexp_5_2(a: uN[8], e: sN[8]) -> uN[8] {
    apfloat::flatten(apfloat::ldexp<u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a), e as s32))
}

pub fn down_rne_5_6_to_5_2(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast_rne<u32:2, u32:5, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a)))
}

pub fn down_even_5_6_to_5_2(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:5, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_EVEN))
}

pub fn down_away_5_6_to_5_2(a: uN[12]) -> uN[8] {
    apfloat::flatten(apfloat::downcast<u32:2, u32:5, u32:6, u32:5>(apfloat::unflatten<u32:5, u32:6>(a), apfloat::RoundStyle::TIES_TO_AWAY))
}

pub fn up_5_2_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_with_denorms<u32:5, u32:6, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}

pub fn updaz_5_2_to_5_6(a: uN[8]) -> uN[12] {
    apfloat::flatten(apfloat::upcast_daz<u32:5, u32:6, u32:5, u32:2>(apfloat::unflatten<u32:5, u32:2>(a)))
}
