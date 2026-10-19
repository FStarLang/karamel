#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn break_in_switch(x: u32)
{ while true { match x { 0u32 => break, 1u32 => while true { break }, _ => break } } }

pub fn break_once() { for _i in 0u32..1u32 { break } }

pub fn continue_once() { for _i in 0u32..1u32 { continue } }

pub fn break_in_for_match(x: u32)
{ for _i in 0u32..2u32 { match x { 0u32 => break, _ => () } } }

pub fn continue_in_for_if(b: bool) { for _i in 0u32..2u32 { if b { continue } } }

pub fn unroll_around_for(b: bool) { for _i in 0u32..1u32 { if b { break } else { continue } } }

pub fn unroll_around_while() { while true { break } }
