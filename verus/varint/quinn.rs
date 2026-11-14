#![feature(panic_internals)]
// Verus proof: quinn-proto's VarInt decode/encode conform to the shared RFC 9000 varint spec.
// Executable code between `// BEGIN UPSTREAM` and `// END UPSTREAM` is quinn main
// c7b46a969cd315398b504792e9e9af6a15a7dcc6 quinn-proto/src/varint.rs, with only Verus
// annotation lines added (checked by conform.py).
use vstd::prelude::*;
mod spec;

verus! {
use crate::spec::*;
use crate::spec::TryInto;
use vstd::arithmetic::power2::{pow2, lemma2_to64, lemma2_to64_rest};

// ---- trusted stand-ins for external items (not upstream code) ----
pub struct UnexpectedEnd;
pub mod coding { pub type Result<T> = ::std::result::Result<T, crate::UnexpectedEnd>; }

/// bytes::Buf: a cursor over the unread bytes `rest()`
pub trait Buf {
    spec fn rest(&self) -> Seq<u8>;
    fn has_remaining(&self) -> (r: bool) ensures r == (self.rest().len() > 0);
    fn remaining(&self) -> (r: usize) ensures r == self.rest().len();
    fn get_u8(&mut self) -> (r: u8)
        requires old(self).rest().len() > 0,
        ensures r == old(self).rest()[0], final(self).rest() == old(self).rest().drop_first();
    fn copy_to_slice(&mut self, dst: &mut [u8])
        requires old(self).rest().len() >= old(dst)@.len(),
        ensures final(dst)@ == old(self).rest().take(old(dst)@.len() as int),
            final(self).rest() == old(self).rest().skip(old(dst)@.len() as int);
}
/// bytes::BufMut: an append-only sink holding `written()`
pub trait BufMut {
    spec fn written(&self) -> Seq<u8>;
    fn put_u8(&mut self, n: u8) ensures final(self).written() == old(self).written().push(n);
    fn put_u16(&mut self, n: u16) ensures exists|b: Seq<u8>| b.len() == 2 && be(b) == n as nat && #[trigger] final(self).written() == old(self).written() + b;
    fn put_u32(&mut self, n: u32) ensures exists|b: Seq<u8>| b.len() == 4 && be(b) == n as nat && #[trigger] final(self).written() == old(self).written() + b;
    fn put_u64(&mut self, n: u64) ensures exists|b: Seq<u8>| b.len() == 8 && be(b) == n as nat && #[trigger] final(self).written() == old(self).written() + b;
}
/// crate::coding::Codec, with the conformance theorem as its contract
pub trait Codec: Sized {
    spec fn value(&self) -> nat;
    spec fn wf(&self) -> bool;
    fn decode<B: Buf>(r: &mut B) -> (res: coding::Result<Self>)
        ensures match decode(old(r).rest()) {
            None => res is Err,
            Some((v, n)) => res matches Ok(x) && x.value() == v && x.wf()
                && final(r).rest() == old(r).rest().skip(n as int),
        };
    fn encode<B: BufMut>(&self, w: &mut B)
        requires self.wf(),
        ensures exists|b: Seq<u8>| #[trigger] final(w).written() == old(w).written() + b
            && b.len() == min_len(self.value()) && decode(b) == Some((self.value(), b.len()));
}
pub assume_specification[ u64::pow ](x: u64, e: u32) -> (r: u64)
    requires x == 2, e < 64,
    ensures r as nat == pow2(e as nat);

pub struct VarInt(pub(crate) u64);

// ---- proofs (not upstream code) ----
proof fn lemma_decode_case(s: Seq<u8>, buf: Seq<u8>, len: nat)
    requires len >= 1, s.len() >= len, buf.len() == len, buf[0] == s[0] & 0x3f,
        buf.drop_first() =~= s.take(len as int).drop_first(),
        len == 1 || len == 2 || len == 4 || len == 8,
    ensures be(buf) == be(s.take(len as int)) % cap(len),
{
    let t = s.take(len as int);
    lemma_be_mod_first(t);
    lemma_be_first(buf);
    let b0 = s[0];
    assert(b0 & 0x3f == b0 % 64) by (bit_vector);
    reveal_with_fuel(pow256, 8);
}

impl Codec for VarInt {
    closed spec fn value(&self) -> nat { self.0 as nat }
    closed spec fn wf(&self) -> bool { self.0 <= max_var_int() }
// BEGIN UPSTREAM
    fn decode<B: Buf>(r: &mut B) -> coding::Result<Self> {
        if !r.has_remaining() {
            return Err(UnexpectedEnd);
        }
        let ghost s = r.rest();
        let mut buf = [0; 8];
        buf[0] = r.get_u8();
        let tag = buf[0] >> 6;
        buf[0] &= 0b0011_1111;
        proof {
            let b0 = s[0];
            assert(b0 >> 6u8 < 4) by (bit_vector);
            assert(b0 & 0x3fu8 < 64) by (bit_vector);
            assert(tag == b0 >> 6u8);
            if tag == 0 {
                assert(b0 >> 6u8 == 0 ==> b0 < 64) by (bit_vector);
                assert(b0 >> 6u8 == 0 ==> b0 & 0x3fu8 == b0) by (bit_vector);
                assert(s.take(1) =~= seq![b0]);
                assert(seq![b0].drop_last() =~= Seq::<u8>::empty());
            }
        }
        let x = match tag {
            0b00 => u64::from(buf[0]),
            0b01 => {
                if r.remaining() < 1 {
                    return Err(UnexpectedEnd);
                }
                r.copy_to_slice(&mut buf[1..2]);
                proof {
                    assert(buf@.subrange(1, 2) =~= s.take(2).drop_first());
                    let bs = buf@.subrange(0, 2);
                    assert(bs.drop_first() =~= s.take(2).drop_first());
                    lemma_decode_case(s, bs, 2);
                    lemma_be_lt_pow(s.take(2));
                    reveal_with_fuel(pow256, 9);
                }
                u64::from(u16::from_be_bytes(buf[..2].try_into().unwrap()))
            }
            0b10 => {
                if r.remaining() < 3 {
                    return Err(UnexpectedEnd);
                }
                r.copy_to_slice(&mut buf[1..4]);
                proof {
                    assert(buf@.subrange(1, 4) =~= s.take(4).drop_first());
                    let bs = buf@.subrange(0, 4);
                    assert(bs.drop_first() =~= s.take(4).drop_first());
                    lemma_decode_case(s, bs, 4);
                    lemma_be_lt_pow(s.take(4));
                    reveal_with_fuel(pow256, 9);
                }
                u64::from(u32::from_be_bytes(buf[..4].try_into().unwrap()))
            }
            0b11 => {
                if r.remaining() < 7 {
                    return Err(UnexpectedEnd);
                }
                r.copy_to_slice(&mut buf[1..8]);
                proof {
                    assert(buf@.subrange(1, 8) =~= s.take(8).drop_first());
                    let bs = buf@;
                    assert(bs.drop_first() =~= s.take(8).drop_first());
                    lemma_decode_case(s, bs, 8);
                    lemma_be_lt_pow(s.take(8));
                    reveal_with_fuel(pow256, 9);
                }
                u64::from_be_bytes(buf)
            }
            _ => unreachable!(),
        };
        Ok(Self(x))
    }
// END UPSTREAM
// BEGIN UPSTREAM
    fn encode<B: BufMut>(&self, w: &mut B) {
        let x = self.0;
        proof { lemma2_to64(); lemma2_to64_rest(); }
        if x < 2u64.pow(6) {
            w.put_u8(x as u8);
            proof { let b = seq![x as u8]; assert(final(w).written() == old(w).written() + b); assert(b.drop_last() =~= Seq::<u8>::empty()); assert(be(b.drop_last()) == 0); assert(be(b) == (x as u8) as nat); assert((x as u8) as nat == x); lemma_encoded(b, x as nat, 1); }
        } else if x < 2u64.pow(14) {
            proof { let y = x as u16; assert(y < 0x4000 ==> (1u16 << 14u16) | y == 0x4000 + y) by (bit_vector); }
            w.put_u16((0b01 << 14) | x as u16);
            proof { let b = choose|b: Seq<u8>| b.len() == 2 && be(b) == ((0b01u16 << 14) | x as u16) as nat && #[trigger] final(w).written() == old(w).written() + b; lemma_encoded(b, x as nat, 2); }
        } else if x < 2u64.pow(30) {
            proof { let y = x as u32; assert(y < 0x4000_0000 ==> (2u32 << 30u32) | y == 0x8000_0000 + y) by (bit_vector); }
            w.put_u32((0b10 << 30) | x as u32);
            proof { let b = choose|b: Seq<u8>| b.len() == 4 && be(b) == ((0b10u32 << 30) | x as u32) as nat && #[trigger] final(w).written() == old(w).written() + b; lemma_encoded(b, x as nat, 4); }
        } else if x < 2u64.pow(62) {
            proof { assert(x < 0x4000_0000_0000_0000 ==> (3u64 << 62u64) | x == 0xc000_0000_0000_0000 + x) by (bit_vector); }
            w.put_u64((0b11 << 62) | x);
            proof { let b = choose|b: Seq<u8>| b.len() == 8 && be(b) == ((0b11u64 << 62) | x) as nat && #[trigger] final(w).written() == old(w).written() + b; lemma_encoded(b, x as nat, 8); }
        } else {
            unreachable!("malformed VarInt")
        }
    }
// END UPSTREAM
}

fn main() {}
} // verus!
