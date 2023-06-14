/* int128 and uint128 implementation */
typedef struct { ulong hi; ulong lo; } secp256k1_uint128;

static void secp256k1_u128_add(secp256k1_uint128 *r, const secp256k1_uint128 *a, const secp256k1_uint128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_u128_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    ulong lowPart = (ulong)a * (ulong)b;
	ulong highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
    uchar carry;
	r->lo = r->lo + a;
	carry = (r->lo < a);
	r->hi = r->hi + carry;
}
static void secp256k1_u128_accum_mul(secp256k1_uint128 *r, ulong a, ulong b) {
    secp256k1_uint128 ab;
    secp256k1_u128_mul(&ab, a, b);

    secp256k1_uint128 temp = *r;
    secp256k1_u128_add(&temp, &temp, &ab);
    *r = temp;
}
static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
    r->lo = a;
}
static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}


// NEEDS TESTING (check negative)
static void secp256k1_u128_rshift(secp256k1_uint128 *r, unsigned int n) {
	r->hi >>= n;
	r->hi |= r->lo << (64 - n);
	r->lo >>= n;
}

// NEEDS TESTING
static ulong secp256k1_u128_hi_u64(const secp256k1_uint128 *a) {
   return a->hi;
}


typedef struct { long hi; ulong lo; } secp256k1_int128;
// NEEDS TESTING (negative carry)
static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
    uchar carry;

    r->lo = a->lo + b->lo;
    carry = (r->lo < a->lo) || (r->lo < b->lo);

    r->hi = a->hi + b->hi + carry;
}
static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
    ulong lowPart = (ulong)a * (ulong)b;
	long highPart = mul_hi(a, b);

	r->lo = lowPart;
	r->hi = highPart;
}
static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
    secp256k1_int128 ab;
    secp256k1_i128_mul(&ab, a, b);

    secp256k1_int128 temp = *r;
    secp256k1_i128_add(&temp, &temp, &ab);
    *r = temp;
}

// NEEDS TESTING
static ulong secp256k1_i128_to_u64(const secp256k1_int128 *a) {
    return a->lo;
}

// NEEDS TESTING (check negative)
static long secp256k1_i128_to_i64(const secp256k1_int128 *a) {
    return (long)a->lo;
}


/* Test Functions */
static long create_long_from_bytes(__global uchar* c, int i) {
	long r = (long)c[i]; // no capes or loops
	r |= (long)c[i + 1] << 8;
	r |= (long)c[i + 2] << 16;
	r |= (long)c[i + 3] << 24;
	r |= (long)c[i + 4] << 32;
	r |= (long)c[i + 5] << 40;
	r |= (long)c[i + 6] << 48;
	return r | (long)c[i + 7] << 56;
}
static void load_bytes_from_int126(const secp256k1_int128 *r, __global uchar* c, int i) {
	long a = r->hi;
	ulong b = r->lo;

    c[i]     = (uchar)b;
    c[i + 1] = (uchar)(b >> 8);
    c[i + 2] = (uchar)(b >> 16);
    c[i + 3] = (uchar)(b >> 24);
    c[i + 4] = (uchar)(b >> 32);
    c[i + 5] = (uchar)(b >> 40);
    c[i + 6] = (uchar)(b >> 48);
    c[i + 7] = (uchar)(b >> 56);

	c[i + 8] = (uchar)a;
    c[i + 9] = (uchar)(a >> 8);
    c[i + 10] = (uchar)(a >> 16);
    c[i + 11] = (uchar)(a >> 24);
    c[i + 12] = (uchar)(a >> 32);
    c[i + 13] = (uchar)(a >> 40);
    c[i + 14] = (uchar)(a >> 48);
    c[i + 15] = (uchar)(a >> 56);
    
	/*
    c[i + 8]  = (uchar)a;
    c[i + 9]  = (uchar)(a >> 8);
    c[i + 10] = (uchar)(a >> 16);
    c[i + 11] = (uchar)(a >> 24);
    c[i + 12] = (uchar)(a >> 32);
    c[i + 13] = (uchar)(a >> 40);
    c[i + 14] = (uchar)(a >> 48);
    c[i + 15] = (uchar)(a >> 56);
	*/
}
static void write_long_bytes(__global uchar* c, long value, int offset) {
	for (ulong i = 0; i < sizeof(long); i++) {
		c[i + offset] = (uchar)((value >> (8 * i)) & 0xFF);
	}
}

__kernel void secp256k1_int128_test_mul(__global uchar* input, __global uchar* output)
{
	// we need 16 bytes to load 2 longs, multiply them and store into a int128 struct
	int i = get_global_id(0) * 16;

	// load the longs
	long a = create_long_from_bytes(input, i); // only high bit is signed
	long b = create_long_from_bytes(input, i + 8);

	// create the int128
	secp256k1_int128 r;

	// multiply the longs
	secp256k1_i128_mul(&r, a, b);

	secp256k1_int128 r2;
	r2.hi = r.hi;
	r2.lo = r.lo;

	secp256k1_i128_add(&r, &r, &r2);

	secp256k1_i128_accum_mul(&r, 4, 4);

	// store the result (16 bytes at a time)
	load_bytes_from_int126(&r, output, i);
}

__kernel void secp256k1_int128_test_sub(__global uchar* input, __global uchar* output)
{

}