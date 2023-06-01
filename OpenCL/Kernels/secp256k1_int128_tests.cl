typedef struct {
    long hi; // Higher 64 bits
    ulong lo; // Lower 64 bits
} secp256k1_int128;

static void secp256k1_i128_add(secp256k1_int128 *r, const secp256k1_int128 *a, const secp256k1_int128 *b) {
    secp256k1_int128 sum;
    secp256k1_int128 carry;

    sum.lo = a->lo + b->lo;
    carry.lo = (sum.lo < a->lo) || (sum.lo < b->lo);

    sum.hi = a->hi + b->hi + carry.lo;
    carry.hi = (sum.hi < a->hi) || (sum.hi < b->hi);

    sum.hi += carry.hi;

    *r = sum;
}

static void secp256k1_i128_mul(secp256k1_int128 *r, long a, long b) {
    ulong lo_a = (ulong)a;
    ulong hi_a = (a < 0) ? ULONG_MAX : 0UL;
    ulong lo_b = (ulong)b;
    ulong hi_b = (b < 0) ? ULONG_MAX : 0UL;

    ulong lo_result = lo_a * lo_b;
    ulong hi_result = mul_hi(lo_a, lo_b);

    ulong mid_result = lo_a * hi_b + hi_a * lo_b;
    mid_result += (lo_result >> 32);
    hi_result += (mid_result >> 32) + ((lo_result >> 32) >> 32);

    r->lo = (lo_result & 0xFFFFFFFFUL) | ((mid_result & 0xFFFFFFFFUL) << 32UL);
    r->hi = hi_result;
}

static void secp256k1_i128_accum_mul(secp256k1_int128 *r, long a, long b) {
    secp256k1_int128 ab;
    secp256k1_i128_mul(&ab, a, b);

    secp256k1_int128 temp = *r;
    secp256k1_i128_add(&temp, &temp, &ab);
    *r = temp;
}

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

static void load_bytes_from_int126(const secp256k1_int128 *r, __global uchar* c, int i)
{
	long a = r->hi;
	long b = r->lo;

    c[i]     = (uchar)b;
    c[i + 1] = (uchar)(b >> 8);
    c[i + 2] = (uchar)(b >> 16);
    c[i + 3] = (uchar)(b >> 24);
    c[i + 4] = (uchar)(b >> 32);
    c[i + 5] = (uchar)(b >> 40);
    c[i + 6] = (uchar)(b >> 48);
    c[i + 7] = (uchar)(b >> 56);
    
    c[i + 8]  = (uchar)a;
    c[i + 9]  = (uchar)(a >> 8);
    c[i + 10] = (uchar)(a >> 16);
    c[i + 11] = (uchar)(a >> 24);
    c[i + 12] = (uchar)(a >> 32);
    c[i + 13] = (uchar)(a >> 40);
    c[i + 14] = (uchar)(a >> 48);
    c[i + 15] = (uchar)(a >> 56);
}

static void write_long_bytes(__global uchar* c, long value, int offset)
{
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

	write_long_bytes(output, r.lo, i);
	write_long_bytes(output, r.hi, i + 8);

	// store the result (16 bytes at a time)
	//load_bytes_from_int126(&r, output, i);

	/*
	// Read 16 bytes from input and store them into output
	output[i] = input[i];
	output[i + 1] = input[i + 1];
	output[i + 2] = input[i + 2];
	output[i + 3] = input[i + 3];
	output[i + 4] = input[i + 4];
	output[i + 5] = input[i + 5];
	output[i + 6] = input[i + 6];
	output[i + 7] = input[i + 7];
	output[i + 8] = input[i + 8];
	output[i + 9] = input[i + 9];
	output[i + 10] = input[i + 10];
	output[i + 11] = input[i + 11];
	output[i + 12] = input[i + 12];
	output[i + 13] = input[i + 13];
	output[i + 14] = input[i + 14];
	output[i + 15] = input[i + 15];
	*/
}
