/* unsigned int128 implementation */
typedef struct { ulong hi; ulong lo; } secp256k1_uint128;

static void secp256k1_u128_from_u64(secp256k1_uint128 *r, ulong a) {
	r->hi = 0;
	r->lo = a;
}
static void secp256k1_u128_add(secp256k1_uint128 *r, const secp256k1_uint128 *a, const secp256k1_uint128 *b) {
	r->lo = a->lo + b->lo;
	r->hi = a->hi + b->hi + (r->lo < a->lo || r->lo < b->lo);
}
static void secp256k1_u128_mul(secp256k1_uint128 *r, ulong a, ulong b) {
	r->lo = (ulong)a * (ulong)b;
	r->hi = mul_hi(a, b);
}
static void secp256k1_u128_accum_u64(secp256k1_uint128 *r, ulong a) {
	r->lo = r->lo + a;
	r->hi += r->lo < a;
}
static void secp256k1_u128_accum_mul(secp256k1_uint128 *r, ulong a, ulong b) {
	secp256k1_uint128 ab;
	secp256k1_u128_mul(&ab, a, b);
	secp256k1_u128_add(r, r, &ab);
}
static void secp256k1_u128_rshift(secp256k1_uint128 *r, unsigned int n) {
	if (n >= 64) {
		r->lo = r->hi >> (n-64);
		r->hi = 0;
	} else if (n > 0) {
		r->lo = ((1U * r->hi) << (64-n)) | r->lo >> n;
		r->hi >>= n;
	}
}
static ulong secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
	return a->lo;
}
static ulong secp256k1_u128_hi_u64(const secp256k1_uint128 *a) {
	return a->hi;
}

/* signed int128 implementation */
typedef struct { long hi; ulong lo; } secp256k1_int128;
static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
	r->lo = a->lo + b->lo;
	r->hi = a->hi + b->hi + (r->lo < a->lo || r->lo < b->lo);
}
static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
	r->lo = (ulong)a * (ulong)b;
	r->hi = mul_hi(a, b);
}
static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
	secp256k1_int128 ab;
	secp256k1_i128_mul(&ab, a, b);
	secp256k1_i128_add(r, r, &ab);
}
static ulong secp256k1_i128_to_u64(const secp256k1_int128 *a) {
	return a->lo;
}
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
	secp256k1_int128 r1;
	r1.lo = a;
	secp256k1_int128 r2;
	r2.lo = b;

	secp256k1_i128_add(&r1, &r1, &r2);

	// store the result (16 bytes at a time)
	//load_bytes_from_int126(&r1, output, i);

	write_long_bytes(output, secp256k1_i128_to_u64(&r1), i);
}
