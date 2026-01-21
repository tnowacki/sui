module deepbook::type_u32;

use std::type_name;
use std::ascii;

public struct TU32<
    phantom Nib8,
    phantom Nib7,
    phantom Nib6,
    phantom Nib5,
    phantom Nib4,
    phantom Nib3,
    phantom Nib2,
    phantom Nib1,
>() has copy, drop, store;

public struct Hex0()
public struct Hex1()
public struct Hex2()
public struct Hex3()
public struct Hex4()
public struct Hex5()
public struct Hex6()
public struct Hex7()
public struct Hex8()
public struct Hex9()
public struct HexA()
public struct HexB()
public struct HexC()
public struct HexD()
public struct HexE()
public struct HexF()

public fun nibbles_to_u32<N8, N7, N6, N5, N4, N3, N2, N1>(
): u32 {
    let n8 = hex_to_u8<N8>() as u32;
    let n7 = hex_to_u8<N7>() as u32;
    let n6 = hex_to_u8<N6>() as u32;
    let n5 = hex_to_u8<N5>() as u32;
    let n4 = hex_to_u8<N4>() as u32;
    let n3 = hex_to_u8<N3>() as u32;
    let n2 = hex_to_u8<N2>() as u32;
    let n1 = hex_to_u8<N1>() as u32;
    n8 << 28 |
    n7 << 24 |
    n6 << 20 |
    n5 << 16 |
    n4 << 12 |
    n3 << 8  |
    n2 << 4  |
    n1
}

public fun hex_to_u8<N>(): u8 {
   assert!(type_name::original_id<N>() == @deepbook);
   let tn = type_name::with_original_ids<N>();
   assert!(tn.module_string().into_bytes() == "type_u32");
   let dt = datatype_string(&tn).as_bytes();
   if (dt == "Hex0") 0x0
   else if (dt == "Hex1") 0x1
   else if (dt == "Hex2") 0x2
   else if (dt == "Hex3") 0x3
   else if (dt == "Hex4") 0x4
   else if (dt == "Hex5") 0x5
   else if (dt == "Hex6") 0x6
   else if (dt == "Hex7") 0x7
   else if (dt == "Hex8") 0x8
   else if (dt == "Hex9") 0x9
   else if (dt == "HexA") 0xA
   else if (dt == "HexB") 0xB
   else if (dt == "HexC") 0xC
   else if (dt == "HexD") 0xD
   else if (dt == "HexE") 0xE
   else if (dt == "HexF") 0xF
   else abort
}

fun datatype_string(_tn: &type_name::TypeName): ascii::String {
    // todo, not sure how this is missing from std::type_name, but it is, so I will make a PR
    abort 0
}
